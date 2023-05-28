/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen

! This file was ported from Lean 3 source module ring_theory.localization.inv_submonoid
! leanprover-community/mathlib commit fe8d0ff42c3c24d789f491dc2622b6cac3d61564
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Submonoid.Inverses
import Mathbin.RingTheory.FiniteType
import Mathbin.RingTheory.Localization.Basic
import Mathbin.Tactic.RingExp

/-!
# Submonoid of inverses

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

 * `is_localization.inv_submonoid M S` is the submonoid of `S = M⁻¹R` consisting of inverses of
   each element `x ∈ M`

## Implementation notes

See `src/ring_theory/localization/basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


variable {R : Type _} [CommRing R] (M : Submonoid R) (S : Type _) [CommRing S]

variable [Algebra R S] {P : Type _} [CommRing P]

open Function

open BigOperators

namespace IsLocalization

section InvSubmonoid

variable (M S)

#print IsLocalization.invSubmonoid /-
/-- The submonoid of `S = M⁻¹R` consisting of `{ 1 / x | x ∈ M }`. -/
def invSubmonoid : Submonoid S :=
  (M.map (algebraMap R S)).left_inv
#align is_localization.inv_submonoid IsLocalization.invSubmonoid
-/

variable [IsLocalization M S]

/- warning: is_localization.submonoid_map_le_is_unit -> IsLocalization.submonoid_map_le_is_unit is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (S : Type.{u2}) [_inst_2 : CommRing.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))] [_inst_5 : IsLocalization.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M S (CommRing.toCommSemiring.{u2} S _inst_2) _inst_3], LE.le.{u2} (Submonoid.{u2} S (Monoid.toMulOneClass.{u2} S (Ring.toMonoid.{u2} S (CommRing.toRing.{u2} S _inst_2)))) (Preorder.toHasLe.{u2} (Submonoid.{u2} S (Monoid.toMulOneClass.{u2} S (Ring.toMonoid.{u2} S (CommRing.toRing.{u2} S _inst_2)))) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} S (Monoid.toMulOneClass.{u2} S (Ring.toMonoid.{u2} S (CommRing.toRing.{u2} S _inst_2)))) (SetLike.partialOrder.{u2, u2} (Submonoid.{u2} S (Monoid.toMulOneClass.{u2} S (Ring.toMonoid.{u2} S (CommRing.toRing.{u2} S _inst_2)))) S (Submonoid.setLike.{u2} S (Monoid.toMulOneClass.{u2} S (Ring.toMonoid.{u2} S (CommRing.toRing.{u2} S _inst_2))))))) (Submonoid.map.{u1, u2, max u1 u2} R S (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Monoid.toMulOneClass.{u2} S (Ring.toMonoid.{u2} S (CommRing.toRing.{u2} S _inst_2))) (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)))) (RingHomClass.toMonoidHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)))) R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))) (RingHom.ringHomClass.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))))) (algebraMap.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)) _inst_3) M) (IsUnit.submonoid.{u2} S (Ring.toMonoid.{u2} S (CommRing.toRing.{u2} S _inst_2)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) (S : Type.{u2}) [_inst_2 : CommRing.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2))] [_inst_5 : IsLocalization.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M S (CommRing.toCommSemiring.{u2} S _inst_2) _inst_3], LE.le.{u2} (Submonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))))) (Preorder.toLE.{u2} (Submonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))))) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))))) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Submonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))))) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Submonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))))) (Submonoid.instCompleteLatticeSubmonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))))))))) (Submonoid.map.{u1, u2, max u1 u2} R S (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2))))) (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))) (RingHomClass.toMonoidHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))) R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2))) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2))))) (algebraMap.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)) _inst_3) M) (IsUnit.submonoid.{u2} S (MonoidWithZero.toMonoid.{u2} S (Semiring.toMonoidWithZero.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))))
Case conversion may be inaccurate. Consider using '#align is_localization.submonoid_map_le_is_unit IsLocalization.submonoid_map_le_is_unitₓ'. -/
theorem submonoid_map_le_is_unit : M.map (algebraMap R S) ≤ IsUnit.submonoid S :=
  by
  rintro _ ⟨a, ha, rfl⟩
  exact IsLocalization.map_units S ⟨_, ha⟩
#align is_localization.submonoid_map_le_is_unit IsLocalization.submonoid_map_le_is_unit

/- warning: is_localization.equiv_inv_submonoid -> IsLocalization.equivInvSubmonoid is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.equiv_inv_submonoid IsLocalization.equivInvSubmonoidₓ'. -/
/-- There is an equivalence of monoids between the image of `M` and `inv_submonoid`. -/
noncomputable abbrev equivInvSubmonoid : M.map (algebraMap R S) ≃* invSubmonoid M S :=
  ((M.map (algebraMap R S)).leftInvEquiv (submonoid_map_le_is_unit M S)).symm
#align is_localization.equiv_inv_submonoid IsLocalization.equivInvSubmonoid

/- warning: is_localization.to_inv_submonoid -> IsLocalization.toInvSubmonoid is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (S : Type.{u2}) [_inst_2 : CommRing.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))] [_inst_5 : IsLocalization.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M S (CommRing.toCommSemiring.{u2} S _inst_2) _inst_3], MonoidHom.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) M) (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))))) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))))) S (Submonoid.setLike.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2))))))) (IsLocalization.invSubmonoid.{u1, u2} R _inst_1 M S _inst_2 _inst_3)) (Submonoid.toMulOneClass.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) M) (Submonoid.toMulOneClass.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2))))) (IsLocalization.invSubmonoid.{u1, u2} R _inst_1 M S _inst_2 _inst_3))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) (S : Type.{u2}) [_inst_2 : CommRing.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2))] [_inst_5 : IsLocalization.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M S (CommRing.toCommSemiring.{u2} S _inst_2) _inst_3], MonoidHom.{u1, u2} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) R (Submonoid.instSetLikeSubmonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))))) x M)) (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Submonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))))) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))))) S (Submonoid.instSetLikeSubmonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2))))))) x (IsLocalization.invSubmonoid.{u1, u2} R _inst_1 M S _inst_2 _inst_3))) (Submonoid.toMulOneClass.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) M) (Submonoid.toMulOneClass.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2))))) (IsLocalization.invSubmonoid.{u1, u2} R _inst_1 M S _inst_2 _inst_3))
Case conversion may be inaccurate. Consider using '#align is_localization.to_inv_submonoid IsLocalization.toInvSubmonoidₓ'. -/
/-- There is a canonical map from `M` to `inv_submonoid` sending `x` to `1 / x`. -/
noncomputable def toInvSubmonoid : M →* invSubmonoid M S :=
  (equivInvSubmonoid M S).toMonoidHom.comp ((algebraMap R S : R →* S).submonoidMap M)
#align is_localization.to_inv_submonoid IsLocalization.toInvSubmonoid

/- warning: is_localization.to_inv_submonoid_surjective -> IsLocalization.toInvSubmonoid_surjective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.to_inv_submonoid_surjective IsLocalization.toInvSubmonoid_surjectiveₓ'. -/
theorem toInvSubmonoid_surjective : Function.Surjective (toInvSubmonoid M S) :=
  Function.Surjective.comp (Equiv.surjective _) (MonoidHom.submonoidMap_surjective _ _)
#align is_localization.to_inv_submonoid_surjective IsLocalization.toInvSubmonoid_surjective

/- warning: is_localization.to_inv_submonoid_mul -> IsLocalization.toInvSubmonoid_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.to_inv_submonoid_mul IsLocalization.toInvSubmonoid_mulₓ'. -/
@[simp]
theorem toInvSubmonoid_mul (m : M) : (toInvSubmonoid M S m : S) * algebraMap R S m = 1 :=
  Submonoid.leftInvEquiv_symm_mul _ _ _
#align is_localization.to_inv_submonoid_mul IsLocalization.toInvSubmonoid_mul

/- warning: is_localization.mul_to_inv_submonoid -> IsLocalization.mul_toInvSubmonoid is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.mul_to_inv_submonoid IsLocalization.mul_toInvSubmonoidₓ'. -/
@[simp]
theorem mul_toInvSubmonoid (m : M) : algebraMap R S m * (toInvSubmonoid M S m : S) = 1 :=
  Submonoid.mul_leftInvEquiv_symm _ _ ⟨_, _⟩
#align is_localization.mul_to_inv_submonoid IsLocalization.mul_toInvSubmonoid

/- warning: is_localization.smul_to_inv_submonoid -> IsLocalization.smul_toInvSubmonoid is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.smul_to_inv_submonoid IsLocalization.smul_toInvSubmonoidₓ'. -/
@[simp]
theorem smul_toInvSubmonoid (m : M) : m • (toInvSubmonoid M S m : S) = 1 :=
  by
  convert mul_to_inv_submonoid M S m
  rw [← Algebra.smul_def]
  rfl
#align is_localization.smul_to_inv_submonoid IsLocalization.smul_toInvSubmonoid

variable {S}

/- warning: is_localization.surj' -> IsLocalization.surj'' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.surj' IsLocalization.surj''ₓ'. -/
theorem surj'' (z : S) : ∃ (r : R)(m : M), z = r • toInvSubmonoid M S m :=
  by
  rcases IsLocalization.surj M z with ⟨⟨r, m⟩, e : z * _ = algebraMap R S r⟩
  refine' ⟨r, m, _⟩
  rw [Algebra.smul_def, ← e, mul_assoc]
  simp
#align is_localization.surj' IsLocalization.surj''

/- warning: is_localization.to_inv_submonoid_eq_mk' -> IsLocalization.toInvSubmonoid_eq_mk' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.to_inv_submonoid_eq_mk' IsLocalization.toInvSubmonoid_eq_mk'ₓ'. -/
theorem toInvSubmonoid_eq_mk' (x : M) : (toInvSubmonoid M S x : S) = mk' S 1 x :=
  by
  rw [← (IsLocalization.map_units S x).mul_left_inj]
  simp
#align is_localization.to_inv_submonoid_eq_mk' IsLocalization.toInvSubmonoid_eq_mk'

/- warning: is_localization.mem_inv_submonoid_iff_exists_mk' -> IsLocalization.mem_invSubmonoid_iff_exists_mk' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) {S : Type.{u2}} [_inst_2 : CommRing.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))] [_inst_5 : IsLocalization.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M S (CommRing.toCommSemiring.{u2} S _inst_2) _inst_3] (x : S), Iff (Membership.Mem.{u2, u2} S (Submonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))))) (SetLike.hasMem.{u2, u2} (Submonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))))) S (Submonoid.setLike.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2))))))) x (IsLocalization.invSubmonoid.{u1, u2} R _inst_1 M S _inst_2 _inst_3)) (Exists.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) M) (fun (m : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) M) => Eq.{succ u2} S (IsLocalization.mk'.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M S (CommRing.toCommSemiring.{u2} S _inst_2) _inst_3 _inst_5 (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))) m) x))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) {S : Type.{u2}} [_inst_2 : CommRing.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2))] [_inst_5 : IsLocalization.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M S (CommRing.toCommSemiring.{u2} S _inst_2) _inst_3] (x : S), Iff (Membership.mem.{u2, u2} S (Submonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))))) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))))) S (Submonoid.instSetLikeSubmonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2))))))) x (IsLocalization.invSubmonoid.{u1, u2} R _inst_1 M S _inst_2 _inst_3)) (Exists.{succ u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) R (Submonoid.instSetLikeSubmonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))))) x M)) (fun (m : Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) R (Submonoid.instSetLikeSubmonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))))) x M)) => Eq.{succ u2} S (IsLocalization.mk'.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M S (CommRing.toCommSemiring.{u2} S _inst_2) _inst_3 _inst_5 (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) m) x))
Case conversion may be inaccurate. Consider using '#align is_localization.mem_inv_submonoid_iff_exists_mk' IsLocalization.mem_invSubmonoid_iff_exists_mk'ₓ'. -/
theorem mem_invSubmonoid_iff_exists_mk' (x : S) : x ∈ invSubmonoid M S ↔ ∃ m : M, mk' S 1 m = x :=
  by
  simp_rw [← to_inv_submonoid_eq_mk']
  exact
    ⟨fun h => ⟨_, congr_arg Subtype.val (to_inv_submonoid_surjective M S ⟨x, h⟩).choose_spec⟩,
      fun h => h.choose_spec ▸ (to_inv_submonoid M S h.some).Prop⟩
#align is_localization.mem_inv_submonoid_iff_exists_mk' IsLocalization.mem_invSubmonoid_iff_exists_mk'

variable (S)

/- warning: is_localization.span_inv_submonoid -> IsLocalization.span_invSubmonoid is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (S : Type.{u2}) [_inst_2 : CommRing.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))] [_inst_5 : IsLocalization.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M S (CommRing.toCommSemiring.{u2} S _inst_2) _inst_3], Eq.{succ u2} (Submodule.{u1, u2} R S (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} S (NonUnitalNonAssocRing.toAddCommGroup.{u2} S (NonAssocRing.toNonUnitalNonAssocRing.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2))))) (Algebra.toModule.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)) _inst_3)) (Submodule.span.{u1, u2} R S (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} S (NonUnitalNonAssocRing.toAddCommGroup.{u2} S (NonAssocRing.toNonUnitalNonAssocRing.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2))))) (Algebra.toModule.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)) _inst_3) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Submonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))))) (Set.{u2} S) (HasLiftT.mk.{succ u2, succ u2} (Submonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))))) (Set.{u2} S) (CoeTCₓ.coe.{succ u2, succ u2} (Submonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))))) (Set.{u2} S) (SetLike.Set.hasCoeT.{u2, u2} (Submonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))))) S (Submonoid.setLike.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2))))))))) (IsLocalization.invSubmonoid.{u1, u2} R _inst_1 M S _inst_2 _inst_3))) (Top.top.{u2} (Submodule.{u1, u2} R S (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} S (NonUnitalNonAssocRing.toAddCommGroup.{u2} S (NonAssocRing.toNonUnitalNonAssocRing.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2))))) (Algebra.toModule.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)) _inst_3)) (Submodule.hasTop.{u1, u2} R S (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} S (NonUnitalNonAssocRing.toAddCommGroup.{u2} S (NonAssocRing.toNonUnitalNonAssocRing.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2))))) (Algebra.toModule.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)) _inst_3)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) (S : Type.{u2}) [_inst_2 : CommRing.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2))] [_inst_5 : IsLocalization.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M S (CommRing.toCommSemiring.{u2} S _inst_2) _inst_3], Eq.{succ u2} (Submodule.{u1, u2} R S (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} S (NonAssocRing.toNonUnitalNonAssocRing.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2))))) (Algebra.toModule.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)) _inst_3)) (Submodule.span.{u1, u2} R S (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} S (NonAssocRing.toNonUnitalNonAssocRing.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2))))) (Algebra.toModule.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)) _inst_3) (SetLike.coe.{u2, u2} (Submonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))))) S (Submonoid.instSetLikeSubmonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))))) (IsLocalization.invSubmonoid.{u1, u2} R _inst_1 M S _inst_2 _inst_3))) (Top.top.{u2} (Submodule.{u1, u2} R S (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} S (NonAssocRing.toNonUnitalNonAssocRing.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2))))) (Algebra.toModule.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)) _inst_3)) (Submodule.instTopSubmodule.{u1, u2} R S (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} S (NonAssocRing.toNonUnitalNonAssocRing.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2))))) (Algebra.toModule.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)) _inst_3)))
Case conversion may be inaccurate. Consider using '#align is_localization.span_inv_submonoid IsLocalization.span_invSubmonoidₓ'. -/
theorem span_invSubmonoid : Submodule.span R (invSubmonoid M S : Set S) = ⊤ :=
  by
  rw [eq_top_iff]
  rintro x -
  rcases IsLocalization.surj'' M x with ⟨r, m, rfl⟩
  exact Submodule.smul_mem _ _ (Submodule.subset_span (to_inv_submonoid M S m).Prop)
#align is_localization.span_inv_submonoid IsLocalization.span_invSubmonoid

/- warning: is_localization.finite_type_of_monoid_fg -> IsLocalization.finiteType_of_monoid_fg is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (S : Type.{u2}) [_inst_2 : CommRing.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))] [_inst_5 : IsLocalization.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M S (CommRing.toCommSemiring.{u2} S _inst_2) _inst_3] [_inst_6 : Monoid.FG.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) M) (Submonoid.toMonoid.{u1} R (Ring.toMonoid.{u1} R (CommRing.toRing.{u1} R _inst_1)) M)], Algebra.FiniteType.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)) _inst_3
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : CommRing.{u2} R] (M : Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))))) (S : Type.{u1}) [_inst_2 : CommRing.{u1} S] [_inst_3 : Algebra.{u2, u1} R S (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2))] [_inst_5 : IsLocalization.{u2, u1} R (CommRing.toCommSemiring.{u2} R _inst_1) M S (CommRing.toCommSemiring.{u1} S _inst_2) _inst_3] [_inst_6 : Monoid.FG.{u2} (Subtype.{succ u2} R (fun (x : R) => Membership.mem.{u2, u2} R (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))))) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))))) R (Submonoid.instSetLikeSubmonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))))))) x M)) (Submonoid.toMonoid.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))) M)], Algebra.FiniteType.{u1, u2} R S (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2)) _inst_3
Case conversion may be inaccurate. Consider using '#align is_localization.finite_type_of_monoid_fg IsLocalization.finiteType_of_monoid_fgₓ'. -/
theorem finiteType_of_monoid_fg [Monoid.FG M] : Algebra.FiniteType R S :=
  by
  have := Monoid.fg_of_surjective _ (to_inv_submonoid_surjective M S)
  rw [Monoid.fg_iff_submonoid_fg] at this
  rcases this with ⟨s, hs⟩
  refine' ⟨⟨s, _⟩⟩
  rw [eq_top_iff]
  rintro x -
  change x ∈ ((Algebra.adjoin R _ : Subalgebra R S).toSubmodule : Set S)
  rw [Algebra.adjoin_eq_span, hs, span_inv_submonoid]
  trivial
#align is_localization.finite_type_of_monoid_fg IsLocalization.finiteType_of_monoid_fg

end InvSubmonoid

end IsLocalization

