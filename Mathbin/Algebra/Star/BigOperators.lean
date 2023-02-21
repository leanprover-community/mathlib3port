/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module algebra.star.big_operators
! leanprover-community/mathlib commit bd9851ca476957ea4549eb19b40e7b5ade9428cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Algebra.Star.Basic

/-! # Big-operators lemmas about `star` algebraic operations

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

These results are kept separate from `algebra.star.basic` to avoid it needing to import `finset`.
-/


variable {R : Type _}

open BigOperators

/- warning: star_prod -> star_prod is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))] {α : Type.{u2}} (s : Finset.{u2} α) (f : α -> R), Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) _inst_2)) (Finset.prod.{u1, u2} R α _inst_1 s (fun (x : α) => f x))) (Finset.prod.{u1, u2} R α _inst_1 s (fun (x : α) => Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) _inst_2)) (f x)))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : CommMonoid.{u2} R] [_inst_2 : StarSemigroup.{u2} R (Monoid.toSemigroup.{u2} R (CommMonoid.toMonoid.{u2} R _inst_1))] {α : Type.{u1}} (s : Finset.{u1} α) (f : α -> R), Eq.{succ u2} R (Star.star.{u2} R (InvolutiveStar.toStar.{u2} R (StarSemigroup.toInvolutiveStar.{u2} R (Monoid.toSemigroup.{u2} R (CommMonoid.toMonoid.{u2} R _inst_1)) _inst_2)) (Finset.prod.{u2, u1} R α _inst_1 s (fun (x : α) => f x))) (Finset.prod.{u2, u1} R α _inst_1 s (fun (x : α) => Star.star.{u2} R (InvolutiveStar.toStar.{u2} R (StarSemigroup.toInvolutiveStar.{u2} R (Monoid.toSemigroup.{u2} R (CommMonoid.toMonoid.{u2} R _inst_1)) _inst_2)) (f x)))
Case conversion may be inaccurate. Consider using '#align star_prod star_prodₓ'. -/
@[simp]
theorem star_prod [CommMonoid R] [StarSemigroup R] {α : Type _} (s : Finset α) (f : α → R) :
    star (∏ x in s, f x) = ∏ x in s, star (f x) :=
  map_prod (starMulAut : R ≃* R) _ _
#align star_prod star_prod

/- warning: star_sum -> star_sum is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} R] [_inst_2 : StarAddMonoid.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_1)] {α : Type.{u2}} (s : Finset.{u2} α) (f : α -> R), Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_1) _inst_2)) (Finset.sum.{u1, u2} R α _inst_1 s (fun (x : α) => f x))) (Finset.sum.{u1, u2} R α _inst_1 s (fun (x : α) => Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_1) _inst_2)) (f x)))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} R] [_inst_2 : StarAddMonoid.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_1)] {α : Type.{u1}} (s : Finset.{u1} α) (f : α -> R), Eq.{succ u2} R (Star.star.{u2} R (InvolutiveStar.toStar.{u2} R (StarAddMonoid.toInvolutiveStar.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_1) _inst_2)) (Finset.sum.{u2, u1} R α _inst_1 s (fun (x : α) => f x))) (Finset.sum.{u2, u1} R α _inst_1 s (fun (x : α) => Star.star.{u2} R (InvolutiveStar.toStar.{u2} R (StarAddMonoid.toInvolutiveStar.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_1) _inst_2)) (f x)))
Case conversion may be inaccurate. Consider using '#align star_sum star_sumₓ'. -/
@[simp]
theorem star_sum [AddCommMonoid R] [StarAddMonoid R] {α : Type _} (s : Finset α) (f : α → R) :
    star (∑ x in s, f x) = ∑ x in s, star (f x) :=
  (starAddEquiv : R ≃+ R).map_sum _ _
#align star_sum star_sum

