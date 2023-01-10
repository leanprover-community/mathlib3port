/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module algebra.star.pi
! leanprover-community/mathlib commit 7b78d1776212a91ecc94cf601f83bdcc46b04213
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Star.Basic
import Mathbin.Algebra.Ring.Pi

/-!
# `star` on pi types

We put a `has_star` structure on pi types that operates elementwise, such that it describes the
complex conjugation of vectors.
-/


universe u v w

variable {I : Type u}

-- The indexing type
variable {f : I → Type v}

-- The family of types already equipped with instances
namespace Pi

instance [∀ i, Star (f i)] : Star (∀ i, f i) where star x i := star (x i)

#print Pi.star_apply /-
@[simp]
theorem star_apply [∀ i, Star (f i)] (x : ∀ i, f i) (i : I) : star x i = star (x i) :=
  rfl
#align pi.star_apply Pi.star_apply
-/

#print Pi.star_def /-
theorem star_def [∀ i, Star (f i)] (x : ∀ i, f i) : star x = fun i => star (x i) :=
  rfl
#align pi.star_def Pi.star_def
-/

instance [∀ i, InvolutiveStar (f i)] : InvolutiveStar (∀ i, f i)
    where star_involutive _ := funext fun _ => star_star _

instance [∀ i, Semigroup (f i)] [∀ i, StarSemigroup (f i)] : StarSemigroup (∀ i, f i)
    where star_mul _ _ := funext fun _ => star_mul _ _

instance [∀ i, AddMonoid (f i)] [∀ i, StarAddMonoid (f i)] : StarAddMonoid (∀ i, f i)
    where star_add _ _ := funext fun _ => star_add _ _

instance [∀ i, NonUnitalSemiring (f i)] [∀ i, StarRing (f i)] : StarRing (∀ i, f i) :=
  { Pi.starAddMonoid, (Pi.starSemigroup : StarSemigroup (∀ i, f i)) with }

instance {R : Type w} [∀ i, HasSmul R (f i)] [Star R] [∀ i, Star (f i)] [∀ i, StarModule R (f i)] :
    StarModule R (∀ i, f i) where star_smul r x := funext fun i => star_smul r (x i)

/- warning: pi.single_star -> Pi.single_star is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {f : I -> Type.{u2}} [_inst_1 : forall (i : I), AddMonoid.{u2} (f i)] [_inst_2 : forall (i : I), StarAddMonoid.{u2} (f i) (_inst_1 i)] [_inst_3 : DecidableEq.{succ u1} I] (i : I) (a : f i), Eq.{max (succ u1) (succ u2)} (forall (i : I), f i) (Pi.single.{u1, u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_3 a b) (fun (i : I) => AddZeroClass.toHasZero.{u2} (f i) (AddMonoid.toAddZeroClass.{u2} (f i) (_inst_1 i))) i (Star.star.{u2} (f i) (InvolutiveStar.toHasStar.{u2} (f i) (StarAddMonoid.toHasInvolutiveStar.{u2} (f i) (_inst_1 i) (_inst_2 i))) a)) (Star.star.{max u1 u2} (forall (i : I), f i) (Pi.hasStar.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => InvolutiveStar.toHasStar.{u2} (f i) (StarAddMonoid.toHasInvolutiveStar.{u2} (f i) (_inst_1 i) (_inst_2 i)))) (Pi.single.{u1, u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_3 a b) (fun (i : I) => AddZeroClass.toHasZero.{u2} (f i) (AddMonoid.toAddZeroClass.{u2} (f i) (_inst_1 i))) i a))
but is expected to have type
  forall {I : Type.{u1}} {f : I -> Type.{u2}} [_inst_1 : forall (i : I), AddMonoid.{u2} (f i)] [_inst_2 : forall (i : I), StarAddMonoid.{u2} (f i) (_inst_1 i)] [_inst_3 : DecidableEq.{succ u1} I] (i : I) (a : f i), Eq.{max (succ u1) (succ u2)} (forall (i : I), f i) (Pi.single.{u1, u2} I f (fun (a : I) (b : I) => _inst_3 a b) (fun (i : I) => AddMonoid.toZero.{u2} (f i) (_inst_1 i)) i (Star.star.{u2} (f i) (InvolutiveStar.toStar.{u2} (f i) (StarAddMonoid.toInvolutiveStar.{u2} (f i) (_inst_1 i) (_inst_2 i))) a)) (Star.star.{max u2 u1} (forall (i : I), f i) (Pi.instStarForAll.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => InvolutiveStar.toStar.{u2} (f i) (StarAddMonoid.toInvolutiveStar.{u2} (f i) (_inst_1 i) (_inst_2 i)))) (Pi.single.{u1, u2} I f (fun (a : I) (b : I) => _inst_3 a b) (fun (i : I) => AddMonoid.toZero.{u2} (f i) (_inst_1 i)) i a))
Case conversion may be inaccurate. Consider using '#align pi.single_star Pi.single_starₓ'. -/
theorem single_star [∀ i, AddMonoid (f i)] [∀ i, StarAddMonoid (f i)] [DecidableEq I] (i : I)
    (a : f i) : Pi.single i (star a) = star (Pi.single i a) :=
  single_op (fun i => @star (f i) _) (fun i => star_zero _) i a
#align pi.single_star Pi.single_star

end Pi

namespace Function

#print Function.update_star /-
theorem update_star [∀ i, Star (f i)] [DecidableEq I] (h : ∀ i : I, f i) (i : I) (a : f i) :
    Function.update (star h) i (star a) = star (Function.update h i a) :=
  funext fun j => (apply_update (fun i => star) h i a j).symm
#align function.update_star Function.update_star
-/

/- warning: function.star_sum_elim -> Function.star_sum_elim is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {J : Type.{u2}} {α : Type.{u3}} (x : I -> α) (y : J -> α) [_inst_1 : Star.{u3} α], Eq.{succ (max (max u1 u2) u3)} ((Sum.{u1, u2} I J) -> α) (Star.star.{max (max u1 u2) u3} ((Sum.{u1, u2} I J) -> α) (Pi.hasStar.{max u1 u2, u3} (Sum.{u1, u2} I J) (fun (ᾰ : Sum.{u1, u2} I J) => α) (fun (i : Sum.{u1, u2} I J) => _inst_1)) (Sum.elim.{u1, u2, succ u3} I J α x y)) (Sum.elim.{u1, u2, succ u3} I J α (Star.star.{max u1 u3} (I -> α) (Pi.hasStar.{u1, u3} I (fun (ᾰ : I) => α) (fun (i : I) => _inst_1)) x) (Star.star.{max u2 u3} (J -> α) (Pi.hasStar.{u2, u3} J (fun (ᾰ : J) => α) (fun (i : J) => _inst_1)) y))
but is expected to have type
  forall {I : Type.{u3}} {J : Type.{u2}} {α : Type.{u1}} (x : I -> α) (y : J -> α) [_inst_1 : Star.{u1} α], Eq.{max (max (succ u3) (succ u2)) (succ u1)} ((Sum.{u3, u2} I J) -> α) (Star.star.{max (max u3 u2) u1} ((Sum.{u3, u2} I J) -> α) (Pi.instStarForAll.{max u3 u2, u1} (Sum.{u3, u2} I J) (fun (ᾰ : Sum.{u3, u2} I J) => α) (fun (i : Sum.{u3, u2} I J) => _inst_1)) (Sum.elim.{u3, u2, succ u1} I J α x y)) (Sum.elim.{u3, u2, succ u1} I J α (Star.star.{max u3 u1} (I -> α) (Pi.instStarForAll.{u3, u1} I (fun (ᾰ : I) => α) (fun (i : I) => _inst_1)) x) (Star.star.{max u1 u2} (J -> α) (Pi.instStarForAll.{u2, u1} J (fun (ᾰ : J) => α) (fun (i : J) => _inst_1)) y))
Case conversion may be inaccurate. Consider using '#align function.star_sum_elim Function.star_sum_elimₓ'. -/
theorem star_sum_elim {I J α : Type _} (x : I → α) (y : J → α) [Star α] :
    star (Sum.elim x y) = Sum.elim (star x) (star y) :=
  by
  ext x
  cases x <;> simp
#align function.star_sum_elim Function.star_sum_elim

end Function

