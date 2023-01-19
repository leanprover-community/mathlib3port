/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module algebra.star.prod
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Star.Basic
import Mathbin.Algebra.Ring.Prod
import Mathbin.Algebra.Module.Prod

/-!
# `star` on product types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We put a `has_star` structure on product types that operates elementwise.
-/


universe u v w

variable {R : Type u} {S : Type v}

namespace Prod

instance [Star R] [Star S] : Star (R × S) where star x := (star x.1, star x.2)

#print Prod.fst_star /-
@[simp]
theorem fst_star [Star R] [Star S] (x : R × S) : (star x).1 = star x.1 :=
  rfl
#align prod.fst_star Prod.fst_star
-/

#print Prod.snd_star /-
@[simp]
theorem snd_star [Star R] [Star S] (x : R × S) : (star x).2 = star x.2 :=
  rfl
#align prod.snd_star Prod.snd_star
-/

#print Prod.star_def /-
theorem star_def [Star R] [Star S] (x : R × S) : star x = (star x.1, star x.2) :=
  rfl
#align prod.star_def Prod.star_def
-/

instance [InvolutiveStar R] [InvolutiveStar S] : InvolutiveStar (R × S)
    where star_involutive _ := Prod.ext (star_star _) (star_star _)

instance [Semigroup R] [Semigroup S] [StarSemigroup R] [StarSemigroup S] : StarSemigroup (R × S)
    where star_mul _ _ := Prod.ext (star_mul _ _) (star_mul _ _)

instance [AddMonoid R] [AddMonoid S] [StarAddMonoid R] [StarAddMonoid S] : StarAddMonoid (R × S)
    where star_add _ _ := Prod.ext (star_add _ _) (star_add _ _)

instance [NonUnitalSemiring R] [NonUnitalSemiring S] [StarRing R] [StarRing S] : StarRing (R × S) :=
  { Prod.starAddMonoid, (Prod.starSemigroup : StarSemigroup (R × S)) with }

instance {α : Type w} [SMul α R] [SMul α S] [Star α] [Star R] [Star S] [StarModule α R]
    [StarModule α S] : StarModule α (R × S)
    where star_smul r x := Prod.ext (star_smul _ _) (star_smul _ _)

end Prod

/- warning: units.embed_product_star -> Units.embed_product_star is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Monoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R _inst_1)] (u : Units.{u1} R _inst_1), Eq.{succ u1} (Prod.{u1, u1} R (MulOpposite.{u1} R)) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (Units.{u1} R _inst_1) (Prod.{u1, u1} R (MulOpposite.{u1} R)) (Units.mulOneClass.{u1} R _inst_1) (Prod.mulOneClass.{u1, u1} R (MulOpposite.{u1} R) (Monoid.toMulOneClass.{u1} R _inst_1) (MulOpposite.mulOneClass.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)))) (fun (_x : MonoidHom.{u1, u1} (Units.{u1} R _inst_1) (Prod.{u1, u1} R (MulOpposite.{u1} R)) (Units.mulOneClass.{u1} R _inst_1) (Prod.mulOneClass.{u1, u1} R (MulOpposite.{u1} R) (Monoid.toMulOneClass.{u1} R _inst_1) (MulOpposite.mulOneClass.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)))) => (Units.{u1} R _inst_1) -> (Prod.{u1, u1} R (MulOpposite.{u1} R))) (MonoidHom.hasCoeToFun.{u1, u1} (Units.{u1} R _inst_1) (Prod.{u1, u1} R (MulOpposite.{u1} R)) (Units.mulOneClass.{u1} R _inst_1) (Prod.mulOneClass.{u1, u1} R (MulOpposite.{u1} R) (Monoid.toMulOneClass.{u1} R _inst_1) (MulOpposite.mulOneClass.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)))) (Units.embedProduct.{u1} R _inst_1) (Star.star.{u1} (Units.{u1} R _inst_1) (InvolutiveStar.toHasStar.{u1} (Units.{u1} R _inst_1) (StarSemigroup.toHasInvolutiveStar.{u1} (Units.{u1} R _inst_1) (Monoid.toSemigroup.{u1} (Units.{u1} R _inst_1) (DivInvMonoid.toMonoid.{u1} (Units.{u1} R _inst_1) (Group.toDivInvMonoid.{u1} (Units.{u1} R _inst_1) (Units.group.{u1} R _inst_1)))) (Units.starSemigroup.{u1} R _inst_1 _inst_2))) u)) (Star.star.{u1} (Prod.{u1, u1} R (MulOpposite.{u1} R)) (Prod.hasStar.{u1, u1} R (MulOpposite.{u1} R) (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) (MulOpposite.hasStar.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)))) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (Units.{u1} R _inst_1) (Prod.{u1, u1} R (MulOpposite.{u1} R)) (Units.mulOneClass.{u1} R _inst_1) (Prod.mulOneClass.{u1, u1} R (MulOpposite.{u1} R) (Monoid.toMulOneClass.{u1} R _inst_1) (MulOpposite.mulOneClass.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)))) (fun (_x : MonoidHom.{u1, u1} (Units.{u1} R _inst_1) (Prod.{u1, u1} R (MulOpposite.{u1} R)) (Units.mulOneClass.{u1} R _inst_1) (Prod.mulOneClass.{u1, u1} R (MulOpposite.{u1} R) (Monoid.toMulOneClass.{u1} R _inst_1) (MulOpposite.mulOneClass.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)))) => (Units.{u1} R _inst_1) -> (Prod.{u1, u1} R (MulOpposite.{u1} R))) (MonoidHom.hasCoeToFun.{u1, u1} (Units.{u1} R _inst_1) (Prod.{u1, u1} R (MulOpposite.{u1} R)) (Units.mulOneClass.{u1} R _inst_1) (Prod.mulOneClass.{u1, u1} R (MulOpposite.{u1} R) (Monoid.toMulOneClass.{u1} R _inst_1) (MulOpposite.mulOneClass.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)))) (Units.embedProduct.{u1} R _inst_1) u))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Monoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R _inst_1)] (u : Units.{u1} R _inst_1), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Units.{u1} R _inst_1) => Prod.{u1, u1} R (MulOpposite.{u1} R)) (Star.star.{u1} (Units.{u1} R _inst_1) (InvolutiveStar.toStar.{u1} (Units.{u1} R _inst_1) (StarSemigroup.toInvolutiveStar.{u1} (Units.{u1} R _inst_1) (Monoid.toSemigroup.{u1} (Units.{u1} R _inst_1) (DivInvMonoid.toMonoid.{u1} (Units.{u1} R _inst_1) (Group.toDivInvMonoid.{u1} (Units.{u1} R _inst_1) (Units.instGroupUnits.{u1} R _inst_1)))) (Units.instStarSemigroupUnitsToSemigroupToMonoidToDivInvMonoidInstGroupUnits.{u1} R _inst_1 _inst_2))) u)) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (Units.{u1} R _inst_1) (Prod.{u1, u1} R (MulOpposite.{u1} R)) (Units.instMulOneClassUnits.{u1} R _inst_1) (Prod.instMulOneClassProd.{u1, u1} R (MulOpposite.{u1} R) (Monoid.toMulOneClass.{u1} R _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)))) (Units.{u1} R _inst_1) (fun (_x : Units.{u1} R _inst_1) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Units.{u1} R _inst_1) => Prod.{u1, u1} R (MulOpposite.{u1} R)) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (Units.{u1} R _inst_1) (Prod.{u1, u1} R (MulOpposite.{u1} R)) (Units.instMulOneClassUnits.{u1} R _inst_1) (Prod.instMulOneClassProd.{u1, u1} R (MulOpposite.{u1} R) (Monoid.toMulOneClass.{u1} R _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)))) (Units.{u1} R _inst_1) (Prod.{u1, u1} R (MulOpposite.{u1} R)) (MulOneClass.toMul.{u1} (Units.{u1} R _inst_1) (Units.instMulOneClassUnits.{u1} R _inst_1)) (MulOneClass.toMul.{u1} (Prod.{u1, u1} R (MulOpposite.{u1} R)) (Prod.instMulOneClassProd.{u1, u1} R (MulOpposite.{u1} R) (Monoid.toMulOneClass.{u1} R _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (Units.{u1} R _inst_1) (Prod.{u1, u1} R (MulOpposite.{u1} R)) (Units.instMulOneClassUnits.{u1} R _inst_1) (Prod.instMulOneClassProd.{u1, u1} R (MulOpposite.{u1} R) (Monoid.toMulOneClass.{u1} R _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)))) (Units.{u1} R _inst_1) (Prod.{u1, u1} R (MulOpposite.{u1} R)) (Units.instMulOneClassUnits.{u1} R _inst_1) (Prod.instMulOneClassProd.{u1, u1} R (MulOpposite.{u1} R) (Monoid.toMulOneClass.{u1} R _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1))) (MonoidHom.monoidHomClass.{u1, u1} (Units.{u1} R _inst_1) (Prod.{u1, u1} R (MulOpposite.{u1} R)) (Units.instMulOneClassUnits.{u1} R _inst_1) (Prod.instMulOneClassProd.{u1, u1} R (MulOpposite.{u1} R) (Monoid.toMulOneClass.{u1} R _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)))))) (Units.embedProduct.{u1} R _inst_1) (Star.star.{u1} (Units.{u1} R _inst_1) (InvolutiveStar.toStar.{u1} (Units.{u1} R _inst_1) (StarSemigroup.toInvolutiveStar.{u1} (Units.{u1} R _inst_1) (Monoid.toSemigroup.{u1} (Units.{u1} R _inst_1) (DivInvMonoid.toMonoid.{u1} (Units.{u1} R _inst_1) (Group.toDivInvMonoid.{u1} (Units.{u1} R _inst_1) (Units.instGroupUnits.{u1} R _inst_1)))) (Units.instStarSemigroupUnitsToSemigroupToMonoidToDivInvMonoidInstGroupUnits.{u1} R _inst_1 _inst_2))) u)) (Star.star.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Units.{u1} R _inst_1) => Prod.{u1, u1} R (MulOpposite.{u1} R)) u) (Prod.instStarProd.{u1, u1} R (MulOpposite.{u1} R) (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) (MulOpposite.instStarMulOpposite.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)))) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (Units.{u1} R _inst_1) (Prod.{u1, u1} R (MulOpposite.{u1} R)) (Units.instMulOneClassUnits.{u1} R _inst_1) (Prod.instMulOneClassProd.{u1, u1} R (MulOpposite.{u1} R) (Monoid.toMulOneClass.{u1} R _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)))) (Units.{u1} R _inst_1) (fun (_x : Units.{u1} R _inst_1) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Units.{u1} R _inst_1) => Prod.{u1, u1} R (MulOpposite.{u1} R)) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (Units.{u1} R _inst_1) (Prod.{u1, u1} R (MulOpposite.{u1} R)) (Units.instMulOneClassUnits.{u1} R _inst_1) (Prod.instMulOneClassProd.{u1, u1} R (MulOpposite.{u1} R) (Monoid.toMulOneClass.{u1} R _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)))) (Units.{u1} R _inst_1) (Prod.{u1, u1} R (MulOpposite.{u1} R)) (MulOneClass.toMul.{u1} (Units.{u1} R _inst_1) (Units.instMulOneClassUnits.{u1} R _inst_1)) (MulOneClass.toMul.{u1} (Prod.{u1, u1} R (MulOpposite.{u1} R)) (Prod.instMulOneClassProd.{u1, u1} R (MulOpposite.{u1} R) (Monoid.toMulOneClass.{u1} R _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (Units.{u1} R _inst_1) (Prod.{u1, u1} R (MulOpposite.{u1} R)) (Units.instMulOneClassUnits.{u1} R _inst_1) (Prod.instMulOneClassProd.{u1, u1} R (MulOpposite.{u1} R) (Monoid.toMulOneClass.{u1} R _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)))) (Units.{u1} R _inst_1) (Prod.{u1, u1} R (MulOpposite.{u1} R)) (Units.instMulOneClassUnits.{u1} R _inst_1) (Prod.instMulOneClassProd.{u1, u1} R (MulOpposite.{u1} R) (Monoid.toMulOneClass.{u1} R _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1))) (MonoidHom.monoidHomClass.{u1, u1} (Units.{u1} R _inst_1) (Prod.{u1, u1} R (MulOpposite.{u1} R)) (Units.instMulOneClassUnits.{u1} R _inst_1) (Prod.instMulOneClassProd.{u1, u1} R (MulOpposite.{u1} R) (Monoid.toMulOneClass.{u1} R _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)))))) (Units.embedProduct.{u1} R _inst_1) u))
Case conversion may be inaccurate. Consider using '#align units.embed_product_star Units.embed_product_starₓ'. -/
@[simp]
theorem Units.embed_product_star [Monoid R] [StarSemigroup R] (u : Rˣ) :
    Units.embedProduct R (star u) = star (Units.embedProduct R u) :=
  rfl
#align units.embed_product_star Units.embed_product_star

