/-
Copyright (c) 2020 Eric Weiser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Weiser

! This file was ported from Lean 3 source module algebra.star.free
! leanprover-community/mathlib commit cb3ceec8485239a61ed51d944cb9a95b68c6bafc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Star.Basic
import Mathbin.Algebra.FreeAlgebra

/-!
# A *-algebra structure on the free algebra.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Reversing words gives a *-structure on the free monoid or on the free algebra on a type.

## Implementation note
We have this in a separate file, rather than in `algebra.free_monoid` and `algebra.free_algebra`,
to avoid importing `algebra.star.basic` into the entire hierarchy.
-/


namespace FreeMonoid

variable {α : Type _}

instance : StarSemigroup (FreeMonoid α)
    where
  unit := List.reverse
  star_involutive := List.reverse_reverse
  star_mul := List.reverse_append

/- warning: free_monoid.star_of -> FreeMonoid.star_of is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (x : α), Eq.{succ u1} (FreeMonoid.{u1} α) (Star.star.{u1} (FreeMonoid.{u1} α) (InvolutiveStar.toHasStar.{u1} (FreeMonoid.{u1} α) (StarSemigroup.toHasInvolutiveStar.{u1} (FreeMonoid.{u1} α) (Monoid.toSemigroup.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α)))) (FreeMonoid.starSemigroup.{u1} α))) (FreeMonoid.of.{u1} α x)) (FreeMonoid.of.{u1} α x)
but is expected to have type
  forall {α : Type.{u1}} (x : α), Eq.{succ u1} (FreeMonoid.{u1} α) (Star.star.{u1} (FreeMonoid.{u1} α) (InvolutiveStar.toStar.{u1} (FreeMonoid.{u1} α) (StarSemigroup.toInvolutiveStar.{u1} (FreeMonoid.{u1} α) (Monoid.toSemigroup.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (FreeMonoid.instStarSemigroupFreeMonoidToSemigroupToMonoidToRightCancelMonoidInstCancelMonoidFreeMonoid.{u1} α))) (FreeMonoid.of.{u1} α x)) (FreeMonoid.of.{u1} α x)
Case conversion may be inaccurate. Consider using '#align free_monoid.star_of FreeMonoid.star_ofₓ'. -/
@[simp]
theorem star_of (x : α) : star (of x) = of x :=
  rfl
#align free_monoid.star_of FreeMonoid.star_of

/- warning: free_monoid.star_one -> FreeMonoid.star_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (FreeMonoid.{u1} α) (Star.star.{u1} (FreeMonoid.{u1} α) (InvolutiveStar.toHasStar.{u1} (FreeMonoid.{u1} α) (StarSemigroup.toHasInvolutiveStar.{u1} (FreeMonoid.{u1} α) (Monoid.toSemigroup.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α)))) (FreeMonoid.starSemigroup.{u1} α))) (OfNat.ofNat.{u1} (FreeMonoid.{u1} α) 1 (OfNat.mk.{u1} (FreeMonoid.{u1} α) 1 (One.one.{u1} (FreeMonoid.{u1} α) (MulOneClass.toHasOne.{u1} (FreeMonoid.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α))))))))) (OfNat.ofNat.{u1} (FreeMonoid.{u1} α) 1 (OfNat.mk.{u1} (FreeMonoid.{u1} α) 1 (One.one.{u1} (FreeMonoid.{u1} α) (MulOneClass.toHasOne.{u1} (FreeMonoid.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α))))))))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (FreeMonoid.{u1} α) (Star.star.{u1} (FreeMonoid.{u1} α) (InvolutiveStar.toStar.{u1} (FreeMonoid.{u1} α) (StarSemigroup.toInvolutiveStar.{u1} (FreeMonoid.{u1} α) (Monoid.toSemigroup.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (FreeMonoid.instStarSemigroupFreeMonoidToSemigroupToMonoidToRightCancelMonoidInstCancelMonoidFreeMonoid.{u1} α))) (OfNat.ofNat.{u1} (FreeMonoid.{u1} α) 1 (One.toOfNat1.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toOne.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))))) (OfNat.ofNat.{u1} (FreeMonoid.{u1} α) 1 (One.toOfNat1.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toOne.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))))
Case conversion may be inaccurate. Consider using '#align free_monoid.star_one FreeMonoid.star_oneₓ'. -/
/-- Note that `star_one` is already a global simp lemma, but this one works with dsimp too -/
@[simp]
theorem star_one : star (1 : FreeMonoid α) = 1 :=
  rfl
#align free_monoid.star_one FreeMonoid.star_one

end FreeMonoid

namespace FreeAlgebra

variable {R : Type _} [CommSemiring R] {X : Type _}

/-- The star ring formed by reversing the elements of products -/
instance : StarRing (FreeAlgebra R X)
    where
  unit := MulOpposite.unop ∘ lift R (MulOpposite.op ∘ ι R)
  star_involutive x := by
    unfold Star.star
    simp only [Function.comp_apply]
    refine' FreeAlgebra.induction R X _ _ _ _ x
    · intros ; simp only [AlgHom.commutes, MulOpposite.algebraMap_apply, MulOpposite.unop_op]
    · intros ; simp only [lift_ι_apply, MulOpposite.unop_op]
    · intros ; simp only [*, map_mul, MulOpposite.unop_mul]
    · intros ; simp only [*, map_add, MulOpposite.unop_add]
  star_mul a b := by simp only [Function.comp_apply, map_mul, MulOpposite.unop_mul]
  star_add a b := by simp only [Function.comp_apply, map_add, MulOpposite.unop_add]

/- warning: free_algebra.star_ι -> FreeAlgebra.star_ι is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {X : Type.{u2}} (x : X), Eq.{succ (max u1 u2)} (FreeAlgebra.{u1, u2} R _inst_1 X) (Star.star.{max u1 u2} (FreeAlgebra.{u1, u2} R _inst_1 X) (InvolutiveStar.toHasStar.{max u1 u2} (FreeAlgebra.{u1, u2} R _inst_1 X) (StarAddMonoid.toHasInvolutiveStar.{max u1 u2} (FreeAlgebra.{u1, u2} R _inst_1 X) (AddCommMonoid.toAddMonoid.{max u1 u2} (FreeAlgebra.{u1, u2} R _inst_1 X) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u1 u2} (FreeAlgebra.{u1, u2} R _inst_1 X) (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (FreeAlgebra.{u1, u2} R _inst_1 X) (Semiring.toNonUnitalSemiring.{max u1 u2} (FreeAlgebra.{u1, u2} R _inst_1 X) (FreeAlgebra.semiring.{u1, u2} R _inst_1 X))))) (StarRing.toStarAddMonoid.{max u1 u2} (FreeAlgebra.{u1, u2} R _inst_1 X) (Semiring.toNonUnitalSemiring.{max u1 u2} (FreeAlgebra.{u1, u2} R _inst_1 X) (FreeAlgebra.semiring.{u1, u2} R _inst_1 X)) (FreeAlgebra.starRing.{u1, u2} R _inst_1 X)))) (FreeAlgebra.ι.{u1, u2} R _inst_1 X x)) (FreeAlgebra.ι.{u1, u2} R _inst_1 X x)
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : CommSemiring.{u2} R] {X : Type.{u1}} (x : X), Eq.{max (succ u2) (succ u1)} (FreeAlgebra.{u2, u1} R _inst_1 X) (Star.star.{max u2 u1} (FreeAlgebra.{u2, u1} R _inst_1 X) (InvolutiveStar.toStar.{max u2 u1} (FreeAlgebra.{u2, u1} R _inst_1 X) (StarAddMonoid.toInvolutiveStar.{max u2 u1} (FreeAlgebra.{u2, u1} R _inst_1 X) (AddMonoidWithOne.toAddMonoid.{max u2 u1} (FreeAlgebra.{u2, u1} R _inst_1 X) (AddCommMonoidWithOne.toAddMonoidWithOne.{max u2 u1} (FreeAlgebra.{u2, u1} R _inst_1 X) (NonAssocSemiring.toAddCommMonoidWithOne.{max u2 u1} (FreeAlgebra.{u2, u1} R _inst_1 X) (Semiring.toNonAssocSemiring.{max u2 u1} (FreeAlgebra.{u2, u1} R _inst_1 X) (FreeAlgebra.instSemiringFreeAlgebra.{u2, u1} R _inst_1 X))))) (StarRing.toStarAddMonoid.{max u2 u1} (FreeAlgebra.{u2, u1} R _inst_1 X) (Semiring.toNonUnitalSemiring.{max u2 u1} (FreeAlgebra.{u2, u1} R _inst_1 X) (FreeAlgebra.instSemiringFreeAlgebra.{u2, u1} R _inst_1 X)) (FreeAlgebra.instStarRingFreeAlgebraToNonUnitalSemiringInstSemiringFreeAlgebra.{u2, u1} R _inst_1 X)))) (FreeAlgebra.ι.{u2, u1} R _inst_1 X x)) (FreeAlgebra.ι.{u2, u1} R _inst_1 X x)
Case conversion may be inaccurate. Consider using '#align free_algebra.star_ι FreeAlgebra.star_ιₓ'. -/
@[simp]
theorem star_ι (x : X) : star (ι R x) = ι R x := by simp [star, Star.star]
#align free_algebra.star_ι FreeAlgebra.star_ι

/- warning: free_algebra.star_algebra_map -> FreeAlgebra.star_algebraMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align free_algebra.star_algebra_map FreeAlgebra.star_algebraMapₓ'. -/
@[simp]
theorem star_algebraMap (r : R) : star (algebraMap R (FreeAlgebra R X) r) = algebraMap R _ r := by
  simp [star, Star.star]
#align free_algebra.star_algebra_map FreeAlgebra.star_algebraMap

/- warning: free_algebra.star_hom -> FreeAlgebra.starHom is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {X : Type.{u2}}, AlgEquiv.{u1, max u1 u2, max u1 u2} R (FreeAlgebra.{u1, u2} R _inst_1 X) (MulOpposite.{max u1 u2} (FreeAlgebra.{u1, u2} R _inst_1 X)) _inst_1 (FreeAlgebra.semiring.{u1, u2} R _inst_1 X) (MulOpposite.semiring.{max u1 u2} (FreeAlgebra.{u1, u2} R _inst_1 X) (FreeAlgebra.semiring.{u1, u2} R _inst_1 X)) (FreeAlgebra.algebra.{u1, u2} R _inst_1 X) (MulOpposite.algebra.{u1, max u1 u2} R (FreeAlgebra.{u1, u2} R _inst_1 X) _inst_1 (FreeAlgebra.semiring.{u1, u2} R _inst_1 X) (FreeAlgebra.algebra.{u1, u2} R _inst_1 X))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {X : Type.{u2}}, AlgEquiv.{u1, max u2 u1, max u2 u1} R (FreeAlgebra.{u1, u2} R _inst_1 X) (MulOpposite.{max u2 u1} (FreeAlgebra.{u1, u2} R _inst_1 X)) _inst_1 (FreeAlgebra.instSemiringFreeAlgebra.{u1, u2} R _inst_1 X) (MulOpposite.semiring.{max u1 u2} (FreeAlgebra.{u1, u2} R _inst_1 X) (FreeAlgebra.instSemiringFreeAlgebra.{u1, u2} R _inst_1 X)) (FreeAlgebra.instAlgebraFreeAlgebraInstSemiringFreeAlgebra.{u1, u2} R _inst_1 X) (MulOpposite.instAlgebraMulOppositeSemiring.{u1, max u1 u2} R (FreeAlgebra.{u1, u2} R _inst_1 X) _inst_1 (FreeAlgebra.instSemiringFreeAlgebra.{u1, u2} R _inst_1 X) (FreeAlgebra.instAlgebraFreeAlgebraInstSemiringFreeAlgebra.{u1, u2} R _inst_1 X))
Case conversion may be inaccurate. Consider using '#align free_algebra.star_hom FreeAlgebra.starHomₓ'. -/
/-- `star` as an `alg_equiv` -/
def starHom : FreeAlgebra R X ≃ₐ[R] (FreeAlgebra R X)ᵐᵒᵖ :=
  { starRingEquiv with commutes' := fun r => by simp [star_algebra_map] }
#align free_algebra.star_hom FreeAlgebra.starHom

end FreeAlgebra

