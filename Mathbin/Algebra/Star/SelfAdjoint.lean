/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis

! This file was ported from Lean 3 source module algebra.star.self_adjoint
! leanprover-community/mathlib commit a6ece35404f60597c651689c1b46ead86de5ac1b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Star.Basic
import Mathbin.GroupTheory.Subgroup.Basic

/-!
# Self-adjoint, skew-adjoint and normal elements of a star additive group

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `self_adjoint R` (resp. `skew_adjoint R`), where `R` is a star additive group,
as the additive subgroup containing the elements that satisfy `star x = x` (resp. `star x = -x`).
This includes, for instance, (skew-)Hermitian operators on Hilbert spaces.

We also define `is_star_normal R`, a `Prop` that states that an element `x` satisfies
`star x * x = x * star x`.

## Implementation notes

* When `R` is a `star_module R₂ R`, then `self_adjoint R` has a natural
  `module (self_adjoint R₂) (self_adjoint R)` structure. However, doing this literally would be
  undesirable since in the main case of interest (`R₂ = ℂ`) we want `module ℝ (self_adjoint R)`
  and not `module (self_adjoint ℂ) (self_adjoint R)`. We solve this issue by adding the typeclass
  `[has_trivial_star R₃]`, of which `ℝ` is an instance (registered in `data/real/basic`), and then
  add a `[module R₃ (self_adjoint R)]` instance whenever we have
  `[module R₃ R] [has_trivial_star R₃]`. (Another approach would have been to define
  `[star_invariant_scalars R₃ R]` to express the fact that `star (x • v) = x • star v`, but
  this typeclass would have the disadvantage of taking two type arguments.)

## TODO

* Define `is_skew_adjoint` to match `is_self_adjoint`.
* Define `λ z x, z * x * star z` (i.e. conjugation by `z`) as a monoid action of `R` on `R`
  (similar to the existing `conj_act` for groups), and then state the fact that `self_adjoint R` is
  invariant under it.

-/


variable {R A : Type _}

#print IsSelfAdjoint /-
/-- An element is self-adjoint if it is equal to its star. -/
def IsSelfAdjoint [Star R] (x : R) : Prop :=
  star x = x
#align is_self_adjoint IsSelfAdjoint
-/

#print IsStarNormal /-
/-- An element of a star monoid is normal if it commutes with its adjoint. -/
class IsStarNormal [Mul R] [Star R] (x : R) : Prop where
  star_comm_self : Commute (star x) x
#align is_star_normal IsStarNormal
-/

export IsStarNormal (star_comm_self)

#print star_comm_self' /-
theorem star_comm_self' [Mul R] [Star R] (x : R) [IsStarNormal x] : star x * x = x * star x :=
  IsStarNormal.star_comm_self
#align star_comm_self' star_comm_self'
-/

namespace IsSelfAdjoint

#print IsSelfAdjoint.all /-
-- named to match `commute.all`
/-- All elements are self-adjoint when `star` is trivial. -/
theorem all [Star R] [TrivialStar R] (r : R) : IsSelfAdjoint r :=
  star_trivial _
#align is_self_adjoint.all IsSelfAdjoint.all
-/

#print IsSelfAdjoint.star_eq /-
theorem star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) : star x = x :=
  hx
#align is_self_adjoint.star_eq IsSelfAdjoint.star_eq
-/

#print isSelfAdjoint_iff /-
theorem isSelfAdjoint_iff [Star R] {x : R} : IsSelfAdjoint x ↔ star x = x :=
  Iff.rfl
#align is_self_adjoint_iff isSelfAdjoint_iff
-/

#print IsSelfAdjoint.star_iff /-
@[simp]
theorem star_iff [InvolutiveStar R] {x : R} : IsSelfAdjoint (star x) ↔ IsSelfAdjoint x := by
  simpa only [IsSelfAdjoint, star_star] using eq_comm
#align is_self_adjoint.star_iff IsSelfAdjoint.star_iff
-/

/- warning: is_self_adjoint.star_mul_self -> IsSelfAdjoint.star_mul_self is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semigroup.{u1} R] [_inst_2 : StarSemigroup.{u1} R _inst_1] (x : R), IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R _inst_1 _inst_2)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Semigroup.toHasMul.{u1} R _inst_1)) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R _inst_1 _inst_2)) x) x)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semigroup.{u1} R] [_inst_2 : StarSemigroup.{u1} R _inst_1] (x : R), IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R _inst_1 _inst_2)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Semigroup.toMul.{u1} R _inst_1)) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R _inst_1 _inst_2)) x) x)
Case conversion may be inaccurate. Consider using '#align is_self_adjoint.star_mul_self IsSelfAdjoint.star_mul_selfₓ'. -/
@[simp]
theorem star_mul_self [Semigroup R] [StarSemigroup R] (x : R) : IsSelfAdjoint (star x * x) := by
  simp only [IsSelfAdjoint, star_mul, star_star]
#align is_self_adjoint.star_mul_self IsSelfAdjoint.star_mul_self

/- warning: is_self_adjoint.mul_star_self -> IsSelfAdjoint.mul_star_self is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semigroup.{u1} R] [_inst_2 : StarSemigroup.{u1} R _inst_1] (x : R), IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R _inst_1 _inst_2)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Semigroup.toHasMul.{u1} R _inst_1)) x (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R _inst_1 _inst_2)) x))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semigroup.{u1} R] [_inst_2 : StarSemigroup.{u1} R _inst_1] (x : R), IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R _inst_1 _inst_2)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Semigroup.toMul.{u1} R _inst_1)) x (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R _inst_1 _inst_2)) x))
Case conversion may be inaccurate. Consider using '#align is_self_adjoint.mul_star_self IsSelfAdjoint.mul_star_selfₓ'. -/
@[simp]
theorem mul_star_self [Semigroup R] [StarSemigroup R] (x : R) : IsSelfAdjoint (x * star x) := by
  simpa only [star_star] using star_mul_self (star x)
#align is_self_adjoint.mul_star_self IsSelfAdjoint.mul_star_self

/- warning: is_self_adjoint.star_hom_apply -> IsSelfAdjoint.starHom_apply is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {R : Type.{u2}} {S : Type.{u3}} [_inst_1 : Star.{u2} R] [_inst_2 : Star.{u3} S] [_inst_3 : StarHomClass.{u1, u2, u3} F R S _inst_1 _inst_2] {x : R}, (IsSelfAdjoint.{u2} R _inst_1 x) -> (forall (f : F), IsSelfAdjoint.{u3} S _inst_2 (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => R -> S) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F R (fun (_x : R) => S) (StarHomClass.toFunLike.{u1, u2, u3} F R S _inst_1 _inst_2 _inst_3)) f x))
but is expected to have type
  forall {F : Type.{u3}} {R : Type.{u2}} {S : Type.{u1}} [_inst_1 : Star.{u2} R] [_inst_2 : Star.{u1} S] [_inst_3 : StarHomClass.{u3, u2, u1} F R S _inst_1 _inst_2] {x : R}, (IsSelfAdjoint.{u2} R _inst_1 x) -> (forall (f : F), IsSelfAdjoint.{u1} ((fun (x._@.Mathlib.Algebra.Star.Basic._hyg.3328 : R) => S) x) _inst_2 (FunLike.coe.{succ u3, succ u2, succ u1} F R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Star.Basic._hyg.3328 : R) => S) _x) (StarHomClass.toFunLike.{u3, u2, u1} F R S _inst_1 _inst_2 _inst_3) f x))
Case conversion may be inaccurate. Consider using '#align is_self_adjoint.star_hom_apply IsSelfAdjoint.starHom_applyₓ'. -/
/-- Functions in a `star_hom_class` preserve self-adjoint elements. -/
theorem starHom_apply {F R S : Type _} [Star R] [Star S] [StarHomClass F R S] {x : R}
    (hx : IsSelfAdjoint x) (f : F) : IsSelfAdjoint (f x) :=
  show star (f x) = f x from map_star f x ▸ congr_arg f hx
#align is_self_adjoint.star_hom_apply IsSelfAdjoint.starHom_apply

section AddMonoid

variable [AddMonoid R] [StarAddMonoid R]

variable (R)

/- warning: is_self_adjoint_zero -> isSelfAdjoint_zero is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : AddMonoid.{u1} R] [_inst_2 : StarAddMonoid.{u1} R _inst_1], IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R _inst_1 _inst_2)) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)))))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : AddMonoid.{u1} R] [_inst_2 : StarAddMonoid.{u1} R _inst_1], IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R _inst_1 _inst_2)) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (AddMonoid.toZero.{u1} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align is_self_adjoint_zero isSelfAdjoint_zeroₓ'. -/
theorem isSelfAdjoint_zero : IsSelfAdjoint (0 : R) :=
  star_zero R
#align is_self_adjoint_zero isSelfAdjoint_zero

variable {R}

/- warning: is_self_adjoint.add -> IsSelfAdjoint.add is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddMonoid.{u1} R] [_inst_2 : StarAddMonoid.{u1} R _inst_1] {x : R} {y : R}, (IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R _inst_1 _inst_2)) x) -> (IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R _inst_1 _inst_2)) y) -> (IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R _inst_1 _inst_2)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1))) x y))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddMonoid.{u1} R] [_inst_2 : StarAddMonoid.{u1} R _inst_1] {x : R} {y : R}, (IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R _inst_1 _inst_2)) x) -> (IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R _inst_1 _inst_2)) y) -> (IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R _inst_1 _inst_2)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1))) x y))
Case conversion may be inaccurate. Consider using '#align is_self_adjoint.add IsSelfAdjoint.addₓ'. -/
theorem add {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x + y) := by
  simp only [isSelfAdjoint_iff, star_add, hx.star_eq, hy.star_eq]
#align is_self_adjoint.add IsSelfAdjoint.add

/- warning: is_self_adjoint.bit0 -> IsSelfAdjoint.bit0 is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddMonoid.{u1} R] [_inst_2 : StarAddMonoid.{u1} R _inst_1] {x : R}, (IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R _inst_1 _inst_2)) x) -> (IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R _inst_1 _inst_2)) (bit0.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) x))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddMonoid.{u1} R] [_inst_2 : StarAddMonoid.{u1} R _inst_1] {x : R}, (IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R _inst_1 _inst_2)) x) -> (IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R _inst_1 _inst_2)) (bit0.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) x))
Case conversion may be inaccurate. Consider using '#align is_self_adjoint.bit0 IsSelfAdjoint.bit0ₓ'. -/
theorem bit0 {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint (bit0 x) := by
  simp only [isSelfAdjoint_iff, star_bit0, hx.star_eq]
#align is_self_adjoint.bit0 IsSelfAdjoint.bit0

end AddMonoid

section AddGroup

variable [AddGroup R] [StarAddMonoid R]

/- warning: is_self_adjoint.neg -> IsSelfAdjoint.neg is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddGroup.{u1} R] [_inst_2 : StarAddMonoid.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1))] {x : R}, (IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) _inst_2)) x) -> (IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) _inst_2)) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) x))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddGroup.{u1} R] [_inst_2 : StarAddMonoid.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1))] {x : R}, (IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) _inst_2)) x) -> (IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) _inst_2)) (Neg.neg.{u1} R (NegZeroClass.toNeg.{u1} R (SubNegZeroMonoid.toNegZeroClass.{u1} R (SubtractionMonoid.toSubNegZeroMonoid.{u1} R (AddGroup.toSubtractionMonoid.{u1} R _inst_1)))) x))
Case conversion may be inaccurate. Consider using '#align is_self_adjoint.neg IsSelfAdjoint.negₓ'. -/
theorem neg {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint (-x) := by
  simp only [isSelfAdjoint_iff, star_neg, hx.star_eq]
#align is_self_adjoint.neg IsSelfAdjoint.neg

/- warning: is_self_adjoint.sub -> IsSelfAdjoint.sub is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddGroup.{u1} R] [_inst_2 : StarAddMonoid.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1))] {x : R} {y : R}, (IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) _inst_2)) x) -> (IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) _inst_2)) y) -> (IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) _inst_2)) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1))) x y))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddGroup.{u1} R] [_inst_2 : StarAddMonoid.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1))] {x : R} {y : R}, (IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) _inst_2)) x) -> (IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) _inst_2)) y) -> (IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) _inst_2)) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1))) x y))
Case conversion may be inaccurate. Consider using '#align is_self_adjoint.sub IsSelfAdjoint.subₓ'. -/
theorem sub {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x - y) := by
  simp only [isSelfAdjoint_iff, star_sub, hx.star_eq, hy.star_eq]
#align is_self_adjoint.sub IsSelfAdjoint.sub

end AddGroup

section AddCommMonoid

variable [AddCommMonoid R] [StarAddMonoid R]

/- warning: is_self_adjoint_add_star_self -> isSelfAdjoint_add_star_self is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} R] [_inst_2 : StarAddMonoid.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_1)] (x : R), IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_1) _inst_2)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_1)))) x (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_1) _inst_2)) x))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} R] [_inst_2 : StarAddMonoid.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_1)] (x : R), IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_1) _inst_2)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_1)))) x (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_1) _inst_2)) x))
Case conversion may be inaccurate. Consider using '#align is_self_adjoint_add_star_self isSelfAdjoint_add_star_selfₓ'. -/
theorem isSelfAdjoint_add_star_self (x : R) : IsSelfAdjoint (x + star x) := by
  simp only [isSelfAdjoint_iff, add_comm, star_add, star_star]
#align is_self_adjoint_add_star_self isSelfAdjoint_add_star_self

/- warning: is_self_adjoint_star_add_self -> isSelfAdjoint_star_add_self is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} R] [_inst_2 : StarAddMonoid.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_1)] (x : R), IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_1) _inst_2)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_1)))) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_1) _inst_2)) x) x)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} R] [_inst_2 : StarAddMonoid.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_1)] (x : R), IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_1) _inst_2)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_1)))) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_1) _inst_2)) x) x)
Case conversion may be inaccurate. Consider using '#align is_self_adjoint_star_add_self isSelfAdjoint_star_add_selfₓ'. -/
theorem isSelfAdjoint_star_add_self (x : R) : IsSelfAdjoint (star x + x) := by
  simp only [isSelfAdjoint_iff, add_comm, star_add, star_star]
#align is_self_adjoint_star_add_self isSelfAdjoint_star_add_self

end AddCommMonoid

section Semigroup

variable [Semigroup R] [StarSemigroup R]

/- warning: is_self_adjoint.conjugate -> IsSelfAdjoint.conjugate is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semigroup.{u1} R] [_inst_2 : StarSemigroup.{u1} R _inst_1] {x : R}, (IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R _inst_1 _inst_2)) x) -> (forall (z : R), IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R _inst_1 _inst_2)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Semigroup.toHasMul.{u1} R _inst_1)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Semigroup.toHasMul.{u1} R _inst_1)) z x) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R _inst_1 _inst_2)) z)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semigroup.{u1} R] [_inst_2 : StarSemigroup.{u1} R _inst_1] {x : R}, (IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R _inst_1 _inst_2)) x) -> (forall (z : R), IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R _inst_1 _inst_2)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Semigroup.toMul.{u1} R _inst_1)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Semigroup.toMul.{u1} R _inst_1)) z x) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R _inst_1 _inst_2)) z)))
Case conversion may be inaccurate. Consider using '#align is_self_adjoint.conjugate IsSelfAdjoint.conjugateₓ'. -/
theorem conjugate {x : R} (hx : IsSelfAdjoint x) (z : R) : IsSelfAdjoint (z * x * star z) := by
  simp only [isSelfAdjoint_iff, star_mul, star_star, mul_assoc, hx.star_eq]
#align is_self_adjoint.conjugate IsSelfAdjoint.conjugate

/- warning: is_self_adjoint.conjugate' -> IsSelfAdjoint.conjugate' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semigroup.{u1} R] [_inst_2 : StarSemigroup.{u1} R _inst_1] {x : R}, (IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R _inst_1 _inst_2)) x) -> (forall (z : R), IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R _inst_1 _inst_2)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Semigroup.toHasMul.{u1} R _inst_1)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Semigroup.toHasMul.{u1} R _inst_1)) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R _inst_1 _inst_2)) z) x) z))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semigroup.{u1} R] [_inst_2 : StarSemigroup.{u1} R _inst_1] {x : R}, (IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R _inst_1 _inst_2)) x) -> (forall (z : R), IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R _inst_1 _inst_2)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Semigroup.toMul.{u1} R _inst_1)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Semigroup.toMul.{u1} R _inst_1)) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R _inst_1 _inst_2)) z) x) z))
Case conversion may be inaccurate. Consider using '#align is_self_adjoint.conjugate' IsSelfAdjoint.conjugate'ₓ'. -/
theorem conjugate' {x : R} (hx : IsSelfAdjoint x) (z : R) : IsSelfAdjoint (star z * x * z) := by
  simp only [isSelfAdjoint_iff, star_mul, star_star, mul_assoc, hx.star_eq]
#align is_self_adjoint.conjugate' IsSelfAdjoint.conjugate'

/- warning: is_self_adjoint.is_star_normal -> IsSelfAdjoint.isStarNormal is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semigroup.{u1} R] [_inst_2 : StarSemigroup.{u1} R _inst_1] {x : R}, (IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R _inst_1 _inst_2)) x) -> (IsStarNormal.{u1} R (Semigroup.toHasMul.{u1} R _inst_1) (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R _inst_1 _inst_2)) x)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semigroup.{u1} R] [_inst_2 : StarSemigroup.{u1} R _inst_1] {x : R}, (IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R _inst_1 _inst_2)) x) -> (IsStarNormal.{u1} R (Semigroup.toMul.{u1} R _inst_1) (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R _inst_1 _inst_2)) x)
Case conversion may be inaccurate. Consider using '#align is_self_adjoint.is_star_normal IsSelfAdjoint.isStarNormalₓ'. -/
theorem isStarNormal {x : R} (hx : IsSelfAdjoint x) : IsStarNormal x :=
  ⟨by simp only [hx.star_eq]⟩
#align is_self_adjoint.is_star_normal IsSelfAdjoint.isStarNormal

end Semigroup

section Monoid

variable [Monoid R] [StarSemigroup R]

variable (R)

/- warning: is_self_adjoint_one -> isSelfAdjoint_one is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Monoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R _inst_1)], IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (MulOneClass.toHasOne.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)))))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : Monoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R _inst_1)], IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Monoid.toOne.{u1} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align is_self_adjoint_one isSelfAdjoint_oneₓ'. -/
theorem isSelfAdjoint_one : IsSelfAdjoint (1 : R) :=
  star_one R
#align is_self_adjoint_one isSelfAdjoint_one

variable {R}

#print IsSelfAdjoint.pow /-
theorem pow {x : R} (hx : IsSelfAdjoint x) (n : ℕ) : IsSelfAdjoint (x ^ n) := by
  simp only [isSelfAdjoint_iff, star_pow, hx.star_eq]
#align is_self_adjoint.pow IsSelfAdjoint.pow
-/

end Monoid

section Semiring

variable [Semiring R] [StarRing R]

/- warning: is_self_adjoint.bit1 -> IsSelfAdjoint.bit1 is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] [_inst_2 : StarRing.{u1} R (Semiring.toNonUnitalSemiring.{u1} R _inst_1)] {x : R}, (IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonUnitalSemiring.{u1} R _inst_1)))) (StarRing.toStarAddMonoid.{u1} R (Semiring.toNonUnitalSemiring.{u1} R _inst_1) _inst_2))) x) -> (IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonUnitalSemiring.{u1} R _inst_1)))) (StarRing.toStarAddMonoid.{u1} R (Semiring.toNonUnitalSemiring.{u1} R _inst_1) _inst_2))) (bit1.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) x))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] [_inst_2 : StarRing.{u1} R (Semiring.toNonUnitalSemiring.{u1} R _inst_1)] {x : R}, (IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (StarRing.toStarAddMonoid.{u1} R (Semiring.toNonUnitalSemiring.{u1} R _inst_1) _inst_2))) x) -> (IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (StarRing.toStarAddMonoid.{u1} R (Semiring.toNonUnitalSemiring.{u1} R _inst_1) _inst_2))) (bit1.{u1} R (Semiring.toOne.{u1} R _inst_1) (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) x))
Case conversion may be inaccurate. Consider using '#align is_self_adjoint.bit1 IsSelfAdjoint.bit1ₓ'. -/
theorem bit1 {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint (bit1 x) := by
  simp only [isSelfAdjoint_iff, star_bit1, hx.star_eq]
#align is_self_adjoint.bit1 IsSelfAdjoint.bit1

#print isSelfAdjoint_natCast /-
@[simp]
theorem isSelfAdjoint_natCast (n : ℕ) : IsSelfAdjoint (n : R) :=
  star_natCast _
#align is_self_adjoint_nat_cast isSelfAdjoint_natCast
-/

end Semiring

section CommSemigroup

variable [CommSemigroup R] [StarSemigroup R]

/- warning: is_self_adjoint.mul -> IsSelfAdjoint.mul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemigroup.{u1} R] [_inst_2 : StarSemigroup.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1)] {x : R} {y : R}, (IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1) _inst_2)) x) -> (IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1) _inst_2)) y) -> (IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1) _inst_2)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Semigroup.toHasMul.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1))) x y))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemigroup.{u1} R] [_inst_2 : StarSemigroup.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1)] {x : R} {y : R}, (IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1) _inst_2)) x) -> (IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1) _inst_2)) y) -> (IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1) _inst_2)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Semigroup.toMul.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1))) x y))
Case conversion may be inaccurate. Consider using '#align is_self_adjoint.mul IsSelfAdjoint.mulₓ'. -/
theorem mul {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x * y) := by
  simp only [isSelfAdjoint_iff, star_mul', hx.star_eq, hy.star_eq]
#align is_self_adjoint.mul IsSelfAdjoint.mul

end CommSemigroup

section Ring

variable [Ring R] [StarRing R]

/- warning: is_self_adjoint_int_cast -> isSelfAdjoint_intCast is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1))] (z : Int), IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1)) _inst_2))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int R (HasLiftT.mk.{1, succ u1} Int R (CoeTCₓ.coe.{1, succ u1} Int R (Int.castCoe.{u1} R (AddGroupWithOne.toHasIntCast.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))))) z)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : StarRing.{u1} R (Semiring.toNonUnitalSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))] (z : Int), IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) (StarRing.toStarAddMonoid.{u1} R (Semiring.toNonUnitalSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) _inst_2))) (Int.cast.{u1} R (Ring.toIntCast.{u1} R _inst_1) z)
Case conversion may be inaccurate. Consider using '#align is_self_adjoint_int_cast isSelfAdjoint_intCastₓ'. -/
@[simp]
theorem isSelfAdjoint_intCast (z : ℤ) : IsSelfAdjoint (z : R) :=
  star_intCast _
#align is_self_adjoint_int_cast isSelfAdjoint_intCast

end Ring

section DivisionSemiring

variable [DivisionSemiring R] [StarRing R]

/- warning: is_self_adjoint.inv -> IsSelfAdjoint.inv is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : DivisionSemiring.{u1} R] [_inst_2 : StarRing.{u1} R (Semiring.toNonUnitalSemiring.{u1} R (DivisionSemiring.toSemiring.{u1} R _inst_1))] {x : R}, (IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonUnitalSemiring.{u1} R (DivisionSemiring.toSemiring.{u1} R _inst_1))))) (StarRing.toStarAddMonoid.{u1} R (Semiring.toNonUnitalSemiring.{u1} R (DivisionSemiring.toSemiring.{u1} R _inst_1)) _inst_2))) x) -> (IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonUnitalSemiring.{u1} R (DivisionSemiring.toSemiring.{u1} R _inst_1))))) (StarRing.toStarAddMonoid.{u1} R (Semiring.toNonUnitalSemiring.{u1} R (DivisionSemiring.toSemiring.{u1} R _inst_1)) _inst_2))) (Inv.inv.{u1} R (DivInvMonoid.toHasInv.{u1} R (GroupWithZero.toDivInvMonoid.{u1} R (DivisionSemiring.toGroupWithZero.{u1} R _inst_1))) x))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : DivisionSemiring.{u1} R] [_inst_2 : StarRing.{u1} R (Semiring.toNonUnitalSemiring.{u1} R (DivisionSemiring.toSemiring.{u1} R _inst_1))] {x : R}, (IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (DivisionSemiring.toSemiring.{u1} R _inst_1))))) (StarRing.toStarAddMonoid.{u1} R (Semiring.toNonUnitalSemiring.{u1} R (DivisionSemiring.toSemiring.{u1} R _inst_1)) _inst_2))) x) -> (IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (DivisionSemiring.toSemiring.{u1} R _inst_1))))) (StarRing.toStarAddMonoid.{u1} R (Semiring.toNonUnitalSemiring.{u1} R (DivisionSemiring.toSemiring.{u1} R _inst_1)) _inst_2))) (Inv.inv.{u1} R (DivisionSemiring.toInv.{u1} R _inst_1) x))
Case conversion may be inaccurate. Consider using '#align is_self_adjoint.inv IsSelfAdjoint.invₓ'. -/
theorem inv {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint x⁻¹ := by
  simp only [isSelfAdjoint_iff, star_inv', hx.star_eq]
#align is_self_adjoint.inv IsSelfAdjoint.inv

#print IsSelfAdjoint.zpow /-
theorem zpow {x : R} (hx : IsSelfAdjoint x) (n : ℤ) : IsSelfAdjoint (x ^ n) := by
  simp only [isSelfAdjoint_iff, star_zpow₀, hx.star_eq]
#align is_self_adjoint.zpow IsSelfAdjoint.zpow
-/

end DivisionSemiring

section DivisionRing

variable [DivisionRing R] [StarRing R]

/- warning: is_self_adjoint_rat_cast -> isSelfAdjoint_ratCast is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : DivisionRing.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))] (x : Rat), IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) _inst_2))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat R (HasLiftT.mk.{1, succ u1} Rat R (CoeTCₓ.coe.{1, succ u1} Rat R (Rat.castCoe.{u1} R (DivisionRing.toHasRatCast.{u1} R _inst_1)))) x)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : DivisionRing.{u1} R] [_inst_2 : StarRing.{u1} R (Semiring.toNonUnitalSemiring.{u1} R (DivisionSemiring.toSemiring.{u1} R (DivisionRing.toDivisionSemiring.{u1} R _inst_1)))] (x : Rat), IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))) (StarRing.toStarAddMonoid.{u1} R (Semiring.toNonUnitalSemiring.{u1} R (DivisionSemiring.toSemiring.{u1} R (DivisionRing.toDivisionSemiring.{u1} R _inst_1))) _inst_2))) (Rat.cast.{u1} R (DivisionRing.toRatCast.{u1} R _inst_1) x)
Case conversion may be inaccurate. Consider using '#align is_self_adjoint_rat_cast isSelfAdjoint_ratCastₓ'. -/
theorem isSelfAdjoint_ratCast (x : ℚ) : IsSelfAdjoint (x : R) :=
  star_ratCast _
#align is_self_adjoint_rat_cast isSelfAdjoint_ratCast

end DivisionRing

section Semifield

variable [Semifield R] [StarRing R]

/- warning: is_self_adjoint.div -> IsSelfAdjoint.div is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semifield.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R (Semifield.toCommSemiring.{u1} R _inst_1)))] {x : R} {y : R}, (IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R (Semifield.toCommSemiring.{u1} R _inst_1)))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R (Semifield.toCommSemiring.{u1} R _inst_1))) _inst_2))) x) -> (IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R (Semifield.toCommSemiring.{u1} R _inst_1)))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R (Semifield.toCommSemiring.{u1} R _inst_1))) _inst_2))) y) -> (IsSelfAdjoint.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R (Semifield.toCommSemiring.{u1} R _inst_1)))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R (Semifield.toCommSemiring.{u1} R _inst_1))) _inst_2))) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (DivInvMonoid.toHasDiv.{u1} R (GroupWithZero.toDivInvMonoid.{u1} R (DivisionSemiring.toGroupWithZero.{u1} R (Semifield.toDivisionSemiring.{u1} R _inst_1))))) x y))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semifield.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R (Semifield.toCommSemiring.{u1} R _inst_1)))] {x : R} {y : R}, (IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (DivisionSemiring.toSemiring.{u1} R (Semifield.toDivisionSemiring.{u1} R _inst_1)))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R (Semifield.toCommSemiring.{u1} R _inst_1))) _inst_2))) x) -> (IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (DivisionSemiring.toSemiring.{u1} R (Semifield.toDivisionSemiring.{u1} R _inst_1)))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R (Semifield.toCommSemiring.{u1} R _inst_1))) _inst_2))) y) -> (IsSelfAdjoint.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (DivisionSemiring.toSemiring.{u1} R (Semifield.toDivisionSemiring.{u1} R _inst_1)))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R (Semifield.toCommSemiring.{u1} R _inst_1))) _inst_2))) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (Semifield.toDiv.{u1} R _inst_1)) x y))
Case conversion may be inaccurate. Consider using '#align is_self_adjoint.div IsSelfAdjoint.divₓ'. -/
theorem div {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x / y) := by
  simp only [isSelfAdjoint_iff, star_div', hx.star_eq, hy.star_eq]
#align is_self_adjoint.div IsSelfAdjoint.div

end Semifield

section SMul

variable [Star R] [AddMonoid A] [StarAddMonoid A] [SMul R A] [StarModule R A]

/- warning: is_self_adjoint.smul -> IsSelfAdjoint.smul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Star.{u1} R] [_inst_2 : AddMonoid.{u2} A] [_inst_3 : StarAddMonoid.{u2} A _inst_2] [_inst_4 : SMul.{u1, u2} R A] [_inst_5 : StarModule.{u1, u2} R A _inst_1 (InvolutiveStar.toHasStar.{u2} A (StarAddMonoid.toHasInvolutiveStar.{u2} A _inst_2 _inst_3)) _inst_4] {r : R}, (IsSelfAdjoint.{u1} R _inst_1 r) -> (forall {x : A}, (IsSelfAdjoint.{u2} A (InvolutiveStar.toHasStar.{u2} A (StarAddMonoid.toHasInvolutiveStar.{u2} A _inst_2 _inst_3)) x) -> (IsSelfAdjoint.{u2} A (InvolutiveStar.toHasStar.{u2} A (StarAddMonoid.toHasInvolutiveStar.{u2} A _inst_2 _inst_3)) (SMul.smul.{u1, u2} R A _inst_4 r x)))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : Star.{u2} R] [_inst_2 : AddMonoid.{u1} A] [_inst_3 : StarAddMonoid.{u1} A _inst_2] [_inst_4 : SMul.{u2, u1} R A] [_inst_5 : StarModule.{u2, u1} R A _inst_1 (InvolutiveStar.toStar.{u1} A (StarAddMonoid.toInvolutiveStar.{u1} A _inst_2 _inst_3)) _inst_4] {r : R}, (IsSelfAdjoint.{u2} R _inst_1 r) -> (forall {x : A}, (IsSelfAdjoint.{u1} A (InvolutiveStar.toStar.{u1} A (StarAddMonoid.toInvolutiveStar.{u1} A _inst_2 _inst_3)) x) -> (IsSelfAdjoint.{u1} A (InvolutiveStar.toStar.{u1} A (StarAddMonoid.toInvolutiveStar.{u1} A _inst_2 _inst_3)) (HSMul.hSMul.{u2, u1, u1} R A A (instHSMul.{u2, u1} R A _inst_4) r x)))
Case conversion may be inaccurate. Consider using '#align is_self_adjoint.smul IsSelfAdjoint.smulₓ'. -/
theorem smul {r : R} (hr : IsSelfAdjoint r) {x : A} (hx : IsSelfAdjoint x) :
    IsSelfAdjoint (r • x) := by simp only [isSelfAdjoint_iff, star_smul, hr.star_eq, hx.star_eq]
#align is_self_adjoint.smul IsSelfAdjoint.smul

end SMul

end IsSelfAdjoint

variable (R)

#print selfAdjoint /-
/-- The self-adjoint elements of a star additive group, as an additive subgroup. -/
def selfAdjoint [AddGroup R] [StarAddMonoid R] : AddSubgroup R
    where
  carrier := { x | IsSelfAdjoint x }
  zero_mem' := star_zero R
  add_mem' _ _ hx := hx.add
  neg_mem' _ hx := hx.neg
#align self_adjoint selfAdjoint
-/

#print skewAdjoint /-
/-- The skew-adjoint elements of a star additive group, as an additive subgroup. -/
def skewAdjoint [AddCommGroup R] [StarAddMonoid R] : AddSubgroup R
    where
  carrier := { x | star x = -x }
  zero_mem' := show star (0 : R) = -0 by simp only [star_zero, neg_zero]
  add_mem' x y (hx : star x = -x) (hy : star y = -y) :=
    show star (x + y) = -(x + y) by rw [star_add x y, hx, hy, neg_add]
  neg_mem' x (hx : star x = -x) := show star (-x) = - -x by simp only [hx, star_neg]
#align skew_adjoint skewAdjoint
-/

variable {R}

namespace selfAdjoint

section AddGroup

variable [AddGroup R] [StarAddMonoid R]

/- warning: self_adjoint.mem_iff -> selfAdjoint.mem_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddGroup.{u1} R] [_inst_2 : StarAddMonoid.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1))] {x : R}, Iff (Membership.Mem.{u1, u1} R (AddSubgroup.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (AddSubgroup.{u1} R _inst_1) R (AddSubgroup.setLike.{u1} R _inst_1)) x (selfAdjoint.{u1} R _inst_1 _inst_2)) (Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) _inst_2)) x) x)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddGroup.{u1} R] [_inst_2 : StarAddMonoid.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1))] {x : R}, Iff (Membership.mem.{u1, u1} R (AddSubgroup.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} R _inst_1) R (AddSubgroup.instSetLikeAddSubgroup.{u1} R _inst_1)) x (selfAdjoint.{u1} R _inst_1 _inst_2)) (Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) _inst_2)) x) x)
Case conversion may be inaccurate. Consider using '#align self_adjoint.mem_iff selfAdjoint.mem_iffₓ'. -/
theorem mem_iff {x : R} : x ∈ selfAdjoint R ↔ star x = x := by rw [← AddSubgroup.mem_carrier];
  exact Iff.rfl
#align self_adjoint.mem_iff selfAdjoint.mem_iff

/- warning: self_adjoint.star_coe_eq -> selfAdjoint.star_val_eq is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddGroup.{u1} R] [_inst_2 : StarAddMonoid.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1))] {x : coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} R _inst_1) R (AddSubgroup.setLike.{u1} R _inst_1)) (selfAdjoint.{u1} R _inst_1 _inst_2)}, Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) _inst_2)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} R _inst_1) R (AddSubgroup.setLike.{u1} R _inst_1)) (selfAdjoint.{u1} R _inst_1 _inst_2)) R (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} R _inst_1) R (AddSubgroup.setLike.{u1} R _inst_1)) (selfAdjoint.{u1} R _inst_1 _inst_2)) R (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} R _inst_1) R (AddSubgroup.setLike.{u1} R _inst_1)) (selfAdjoint.{u1} R _inst_1 _inst_2)) R (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} R _inst_1) R (AddSubgroup.setLike.{u1} R _inst_1)) (selfAdjoint.{u1} R _inst_1 _inst_2)) R (coeSubtype.{succ u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (AddSubgroup.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (AddSubgroup.{u1} R _inst_1) R (AddSubgroup.setLike.{u1} R _inst_1)) x (selfAdjoint.{u1} R _inst_1 _inst_2)))))) x)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} R _inst_1) R (AddSubgroup.setLike.{u1} R _inst_1)) (selfAdjoint.{u1} R _inst_1 _inst_2)) R (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} R _inst_1) R (AddSubgroup.setLike.{u1} R _inst_1)) (selfAdjoint.{u1} R _inst_1 _inst_2)) R (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} R _inst_1) R (AddSubgroup.setLike.{u1} R _inst_1)) (selfAdjoint.{u1} R _inst_1 _inst_2)) R (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} R _inst_1) R (AddSubgroup.setLike.{u1} R _inst_1)) (selfAdjoint.{u1} R _inst_1 _inst_2)) R (coeSubtype.{succ u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (AddSubgroup.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (AddSubgroup.{u1} R _inst_1) R (AddSubgroup.setLike.{u1} R _inst_1)) x (selfAdjoint.{u1} R _inst_1 _inst_2)))))) x)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddGroup.{u1} R] [_inst_2 : StarAddMonoid.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1))] {x : Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (AddSubgroup.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} R _inst_1) R (AddSubgroup.instSetLikeAddSubgroup.{u1} R _inst_1)) x (selfAdjoint.{u1} R _inst_1 _inst_2))}, Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) _inst_2)) (Subtype.val.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x (SetLike.coe.{u1, u1} (AddSubgroup.{u1} R _inst_1) R (AddSubgroup.instSetLikeAddSubgroup.{u1} R _inst_1) (selfAdjoint.{u1} R _inst_1 _inst_2))) x)) (Subtype.val.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x (SetLike.coe.{u1, u1} (AddSubgroup.{u1} R _inst_1) R (AddSubgroup.instSetLikeAddSubgroup.{u1} R _inst_1) (selfAdjoint.{u1} R _inst_1 _inst_2))) x)
Case conversion may be inaccurate. Consider using '#align self_adjoint.star_coe_eq selfAdjoint.star_val_eqₓ'. -/
@[simp, norm_cast]
theorem star_val_eq {x : selfAdjoint R} : star (x : R) = x :=
  x.Prop
#align self_adjoint.star_coe_eq selfAdjoint.star_val_eq

instance : Inhabited (selfAdjoint R) :=
  ⟨0⟩

end AddGroup

section Ring

variable [Ring R] [StarRing R]

instance : One (selfAdjoint R) :=
  ⟨⟨1, isSelfAdjoint_one R⟩⟩

#print selfAdjoint.val_one /-
@[simp, norm_cast]
theorem val_one : ↑(1 : selfAdjoint R) = (1 : R) :=
  rfl
#align self_adjoint.coe_one selfAdjoint.val_one
-/

instance [Nontrivial R] : Nontrivial (selfAdjoint R) :=
  ⟨⟨0, 1, Subtype.ne_of_val_ne zero_ne_one⟩⟩

instance : NatCast (selfAdjoint R) :=
  ⟨fun n => ⟨n, isSelfAdjoint_natCast _⟩⟩

instance : IntCast (selfAdjoint R) :=
  ⟨fun n => ⟨n, isSelfAdjoint_intCast _⟩⟩

instance : Pow (selfAdjoint R) ℕ :=
  ⟨fun x n => ⟨(x : R) ^ n, x.Prop.pow n⟩⟩

/- warning: self_adjoint.coe_pow -> selfAdjoint.val_pow is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align self_adjoint.coe_pow selfAdjoint.val_powₓ'. -/
@[simp, norm_cast]
theorem val_pow (x : selfAdjoint R) (n : ℕ) : ↑(x ^ n) = (x : R) ^ n :=
  rfl
#align self_adjoint.coe_pow selfAdjoint.val_pow

end Ring

section NonUnitalCommRing

variable [NonUnitalCommRing R] [StarRing R]

instance : Mul (selfAdjoint R) :=
  ⟨fun x y => ⟨(x : R) * y, x.Prop.mul y.Prop⟩⟩

/- warning: self_adjoint.coe_mul -> selfAdjoint.val_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align self_adjoint.coe_mul selfAdjoint.val_mulₓ'. -/
@[simp, norm_cast]
theorem val_mul (x y : selfAdjoint R) : ↑(x * y) = (x : R) * y :=
  rfl
#align self_adjoint.coe_mul selfAdjoint.val_mul

end NonUnitalCommRing

section CommRing

variable [CommRing R] [StarRing R]

instance : CommRing (selfAdjoint R) :=
  Function.Injective.commRing _ Subtype.coe_injective (selfAdjoint R).val_zero val_one
    (selfAdjoint R).val_add val_mul (selfAdjoint R).coe_neg (selfAdjoint R).val_neg_eq_neg_val
    (selfAdjoint R).val_nsmul_eq_nsmul_val (selfAdjoint R).val_zsmul_eq_zsmul_val val_pow
    (fun _ => rfl) fun _ => rfl

end CommRing

section Field

variable [Field R] [StarRing R]

instance : Inv (selfAdjoint R) where inv x := ⟨x.val⁻¹, x.Prop.inv⟩

/- warning: self_adjoint.coe_inv -> selfAdjoint.val_inv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align self_adjoint.coe_inv selfAdjoint.val_invₓ'. -/
@[simp, norm_cast]
theorem val_inv (x : selfAdjoint R) : ↑x⁻¹ = (x : R)⁻¹ :=
  rfl
#align self_adjoint.coe_inv selfAdjoint.val_inv

instance : Div (selfAdjoint R) where div x y := ⟨x / y, x.Prop.div y.Prop⟩

/- warning: self_adjoint.coe_div -> selfAdjoint.val_div is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align self_adjoint.coe_div selfAdjoint.val_divₓ'. -/
@[simp, norm_cast]
theorem val_div (x y : selfAdjoint R) : ↑(x / y) = (x / y : R) :=
  rfl
#align self_adjoint.coe_div selfAdjoint.val_div

instance : Pow (selfAdjoint R) ℤ where pow x z := ⟨x ^ z, x.Prop.zpow z⟩

/- warning: self_adjoint.coe_zpow -> selfAdjoint.val_zpow is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align self_adjoint.coe_zpow selfAdjoint.val_zpowₓ'. -/
@[simp, norm_cast]
theorem val_zpow (x : selfAdjoint R) (z : ℤ) : ↑(x ^ z) = (x : R) ^ z :=
  rfl
#align self_adjoint.coe_zpow selfAdjoint.val_zpow

instance : HasRatCast (selfAdjoint R) :=
  ⟨fun n => ⟨n, isSelfAdjoint_ratCast n⟩⟩

/- warning: self_adjoint.coe_rat_cast -> selfAdjoint.val_ratCast is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align self_adjoint.coe_rat_cast selfAdjoint.val_ratCastₓ'. -/
@[simp, norm_cast]
theorem val_ratCast (x : ℚ) : ↑(x : selfAdjoint R) = (x : R) :=
  rfl
#align self_adjoint.coe_rat_cast selfAdjoint.val_ratCast

/- warning: self_adjoint.has_qsmul -> selfAdjoint.instQSMul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Field.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (Field.toCommRing.{u1} R _inst_1))))], SMul.{0, u1} Rat (coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_1)))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_1)))))) R (AddSubgroup.setLike.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_1))))))) (selfAdjoint.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_1))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (Field.toCommRing.{u1} R _inst_1)))) _inst_2)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Field.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalCommSemiring.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (Field.toCommRing.{u1} R _inst_1))))], SMul.{0, u1} Rat (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_1))))) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_1))))) R (AddSubgroup.instSetLikeAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_1)))))) x (selfAdjoint.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_1)))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalCommSemiring.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (Field.toCommRing.{u1} R _inst_1)))) _inst_2))))
Case conversion may be inaccurate. Consider using '#align self_adjoint.has_qsmul selfAdjoint.instQSMulₓ'. -/
instance instQSMul : SMul ℚ (selfAdjoint R) :=
  ⟨fun a x =>
    ⟨a • x, by rw [Rat.smul_def] <;> exact IsSelfAdjoint.mul (isSelfAdjoint_ratCast a) x.prop⟩⟩
#align self_adjoint.has_qsmul selfAdjoint.instQSMul

/- warning: self_adjoint.coe_rat_smul -> selfAdjoint.val_rat_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align self_adjoint.coe_rat_smul selfAdjoint.val_rat_smulₓ'. -/
@[simp, norm_cast]
theorem val_rat_smul (x : selfAdjoint R) (a : ℚ) : ↑(a • x) = a • (x : R) :=
  rfl
#align self_adjoint.coe_rat_smul selfAdjoint.val_rat_smul

instance : Field (selfAdjoint R) :=
  Function.Injective.field _ Subtype.coe_injective (selfAdjoint R).val_zero val_one
    (selfAdjoint R).val_add val_mul (selfAdjoint R).coe_neg (selfAdjoint R).val_neg_eq_neg_val
    val_inv val_div (selfAdjoint R).val_nsmul_eq_nsmul_val (selfAdjoint R).val_zsmul_eq_zsmul_val
    val_rat_smul val_pow val_zpow (fun _ => rfl) (fun _ => rfl) val_ratCast

end Field

section SMul

variable [Star R] [TrivialStar R] [AddGroup A] [StarAddMonoid A]

instance [SMul R A] [StarModule R A] : SMul R (selfAdjoint A) :=
  ⟨fun r x => ⟨r • x, (IsSelfAdjoint.all _).smul x.Prop⟩⟩

/- warning: self_adjoint.coe_smul -> selfAdjoint.val_smul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Star.{u1} R] [_inst_2 : TrivialStar.{u1} R _inst_1] [_inst_3 : AddGroup.{u2} A] [_inst_4 : StarAddMonoid.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_3))] [_inst_5 : SMul.{u1, u2} R A] [_inst_6 : StarModule.{u1, u2} R A _inst_1 (InvolutiveStar.toHasStar.{u2} A (StarAddMonoid.toHasInvolutiveStar.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A _inst_3)) _inst_4)) _inst_5] (r : R) (x : coeSort.{succ u2, succ (succ u2)} (AddSubgroup.{u2} A _inst_3) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (AddSubgroup.{u2} A _inst_3) A (AddSubgroup.setLike.{u2} A _inst_3)) (selfAdjoint.{u2} A _inst_3 _inst_4)), Eq.{succ u2} A ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (AddSubgroup.{u2} A _inst_3) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (AddSubgroup.{u2} A _inst_3) A (AddSubgroup.setLike.{u2} A _inst_3)) (selfAdjoint.{u2} A _inst_3 _inst_4)) A (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (AddSubgroup.{u2} A _inst_3) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (AddSubgroup.{u2} A _inst_3) A (AddSubgroup.setLike.{u2} A _inst_3)) (selfAdjoint.{u2} A _inst_3 _inst_4)) A (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (AddSubgroup.{u2} A _inst_3) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (AddSubgroup.{u2} A _inst_3) A (AddSubgroup.setLike.{u2} A _inst_3)) (selfAdjoint.{u2} A _inst_3 _inst_4)) A (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (AddSubgroup.{u2} A _inst_3) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (AddSubgroup.{u2} A _inst_3) A (AddSubgroup.setLike.{u2} A _inst_3)) (selfAdjoint.{u2} A _inst_3 _inst_4)) A (coeSubtype.{succ u2} A (fun (x : A) => Membership.Mem.{u2, u2} A (AddSubgroup.{u2} A _inst_3) (SetLike.hasMem.{u2, u2} (AddSubgroup.{u2} A _inst_3) A (AddSubgroup.setLike.{u2} A _inst_3)) x (selfAdjoint.{u2} A _inst_3 _inst_4)))))) (SMul.smul.{u1, u2} R (coeSort.{succ u2, succ (succ u2)} (AddSubgroup.{u2} A _inst_3) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (AddSubgroup.{u2} A _inst_3) A (AddSubgroup.setLike.{u2} A _inst_3)) (selfAdjoint.{u2} A _inst_3 _inst_4)) (selfAdjoint.hasSmul.{u1, u2} R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6) r x)) (SMul.smul.{u1, u2} R A _inst_5 r ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (AddSubgroup.{u2} A _inst_3) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (AddSubgroup.{u2} A _inst_3) A (AddSubgroup.setLike.{u2} A _inst_3)) (selfAdjoint.{u2} A _inst_3 _inst_4)) A (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (AddSubgroup.{u2} A _inst_3) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (AddSubgroup.{u2} A _inst_3) A (AddSubgroup.setLike.{u2} A _inst_3)) (selfAdjoint.{u2} A _inst_3 _inst_4)) A (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (AddSubgroup.{u2} A _inst_3) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (AddSubgroup.{u2} A _inst_3) A (AddSubgroup.setLike.{u2} A _inst_3)) (selfAdjoint.{u2} A _inst_3 _inst_4)) A (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (AddSubgroup.{u2} A _inst_3) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (AddSubgroup.{u2} A _inst_3) A (AddSubgroup.setLike.{u2} A _inst_3)) (selfAdjoint.{u2} A _inst_3 _inst_4)) A (coeSubtype.{succ u2} A (fun (x : A) => Membership.Mem.{u2, u2} A (AddSubgroup.{u2} A _inst_3) (SetLike.hasMem.{u2, u2} (AddSubgroup.{u2} A _inst_3) A (AddSubgroup.setLike.{u2} A _inst_3)) x (selfAdjoint.{u2} A _inst_3 _inst_4)))))) x))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : Star.{u2} R] [_inst_2 : TrivialStar.{u2} R _inst_1] [_inst_3 : AddGroup.{u1} A] [_inst_4 : StarAddMonoid.{u1} A (SubNegMonoid.toAddMonoid.{u1} A (AddGroup.toSubNegMonoid.{u1} A _inst_3))] [_inst_5 : SMul.{u2, u1} R A] [_inst_6 : StarModule.{u2, u1} R A _inst_1 (InvolutiveStar.toStar.{u1} A (StarAddMonoid.toInvolutiveStar.{u1} A (SubNegMonoid.toAddMonoid.{u1} A (AddGroup.toSubNegMonoid.{u1} A _inst_3)) _inst_4)) _inst_5] (r : R) (x : Subtype.{succ u1} A (fun (x : A) => Membership.mem.{u1, u1} A (AddSubgroup.{u1} A _inst_3) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} A _inst_3) A (AddSubgroup.instSetLikeAddSubgroup.{u1} A _inst_3)) x (selfAdjoint.{u1} A _inst_3 _inst_4))), Eq.{succ u1} A (Subtype.val.{succ u1} A (fun (x : A) => Membership.mem.{u1, u1} A (Set.{u1} A) (Set.instMembershipSet.{u1} A) x (SetLike.coe.{u1, u1} (AddSubgroup.{u1} A _inst_3) A (AddSubgroup.instSetLikeAddSubgroup.{u1} A _inst_3) (selfAdjoint.{u1} A _inst_3 _inst_4))) (HSMul.hSMul.{u2, u1, u1} R (Subtype.{succ u1} A (fun (x : A) => Membership.mem.{u1, u1} A (AddSubgroup.{u1} A _inst_3) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} A _inst_3) A (AddSubgroup.instSetLikeAddSubgroup.{u1} A _inst_3)) x (selfAdjoint.{u1} A _inst_3 _inst_4))) (Subtype.{succ u1} A (fun (x : A) => Membership.mem.{u1, u1} A (AddSubgroup.{u1} A _inst_3) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} A _inst_3) A (AddSubgroup.instSetLikeAddSubgroup.{u1} A _inst_3)) x (selfAdjoint.{u1} A _inst_3 _inst_4))) (instHSMul.{u2, u1} R (Subtype.{succ u1} A (fun (x : A) => Membership.mem.{u1, u1} A (AddSubgroup.{u1} A _inst_3) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} A _inst_3) A (AddSubgroup.instSetLikeAddSubgroup.{u1} A _inst_3)) x (selfAdjoint.{u1} A _inst_3 _inst_4))) (selfAdjoint.instSMulSubtypeMemAddSubgroupInstMembershipInstSetLikeAddSubgroupSelfAdjoint.{u2, u1} R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6)) r x)) (HSMul.hSMul.{u2, u1, u1} R A A (instHSMul.{u2, u1} R A _inst_5) r (Subtype.val.{succ u1} A (fun (x : A) => Membership.mem.{u1, u1} A (Set.{u1} A) (Set.instMembershipSet.{u1} A) x (SetLike.coe.{u1, u1} (AddSubgroup.{u1} A _inst_3) A (AddSubgroup.instSetLikeAddSubgroup.{u1} A _inst_3) (selfAdjoint.{u1} A _inst_3 _inst_4))) x))
Case conversion may be inaccurate. Consider using '#align self_adjoint.coe_smul selfAdjoint.val_smulₓ'. -/
@[simp, norm_cast]
theorem val_smul [SMul R A] [StarModule R A] (r : R) (x : selfAdjoint A) : ↑(r • x) = r • (x : A) :=
  rfl
#align self_adjoint.coe_smul selfAdjoint.val_smul

instance [Monoid R] [MulAction R A] [StarModule R A] : MulAction R (selfAdjoint A) :=
  Function.Injective.mulAction coe Subtype.coe_injective val_smul

instance [Monoid R] [DistribMulAction R A] [StarModule R A] : DistribMulAction R (selfAdjoint A) :=
  Function.Injective.distribMulAction (selfAdjoint A).Subtype Subtype.coe_injective val_smul

end SMul

section Module

variable [Star R] [TrivialStar R] [AddCommGroup A] [StarAddMonoid A]

instance [Semiring R] [Module R A] [StarModule R A] : Module R (selfAdjoint A) :=
  Function.Injective.module R (selfAdjoint A).Subtype Subtype.coe_injective val_smul

end Module

end selfAdjoint

namespace skewAdjoint

section AddGroup

variable [AddCommGroup R] [StarAddMonoid R]

/- warning: skew_adjoint.mem_iff -> skewAdjoint.mem_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddCommGroup.{u1} R] [_inst_2 : StarAddMonoid.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)))] {x : R}, Iff (Membership.Mem.{u1, u1} R (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) (SetLike.hasMem.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) R (AddSubgroup.setLike.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1))) x (skewAdjoint.{u1} R _inst_1 _inst_2)) (Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1))) _inst_2)) x) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1))) x))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddCommGroup.{u1} R] [_inst_2 : StarAddMonoid.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)))] {x : R}, Iff (Membership.mem.{u1, u1} R (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) R (AddSubgroup.instSetLikeAddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1))) x (skewAdjoint.{u1} R _inst_1 _inst_2)) (Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1))) _inst_2)) x) (Neg.neg.{u1} R (NegZeroClass.toNeg.{u1} R (SubNegZeroMonoid.toNegZeroClass.{u1} R (SubtractionMonoid.toSubNegZeroMonoid.{u1} R (SubtractionCommMonoid.toSubtractionMonoid.{u1} R (AddCommGroup.toDivisionAddCommMonoid.{u1} R _inst_1))))) x))
Case conversion may be inaccurate. Consider using '#align skew_adjoint.mem_iff skewAdjoint.mem_iffₓ'. -/
theorem mem_iff {x : R} : x ∈ skewAdjoint R ↔ star x = -x := by rw [← AddSubgroup.mem_carrier];
  exact Iff.rfl
#align skew_adjoint.mem_iff skewAdjoint.mem_iff

/- warning: skew_adjoint.star_coe_eq -> skewAdjoint.star_val_eq is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddCommGroup.{u1} R] [_inst_2 : StarAddMonoid.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)))] {x : coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) R (AddSubgroup.setLike.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1))) (skewAdjoint.{u1} R _inst_1 _inst_2)}, Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1))) _inst_2)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) R (AddSubgroup.setLike.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1))) (skewAdjoint.{u1} R _inst_1 _inst_2)) R (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) R (AddSubgroup.setLike.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1))) (skewAdjoint.{u1} R _inst_1 _inst_2)) R (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) R (AddSubgroup.setLike.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1))) (skewAdjoint.{u1} R _inst_1 _inst_2)) R (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) R (AddSubgroup.setLike.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1))) (skewAdjoint.{u1} R _inst_1 _inst_2)) R (coeSubtype.{succ u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) (SetLike.hasMem.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) R (AddSubgroup.setLike.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1))) x (skewAdjoint.{u1} R _inst_1 _inst_2)))))) x)) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) R (AddSubgroup.setLike.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1))) (skewAdjoint.{u1} R _inst_1 _inst_2)) R (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) R (AddSubgroup.setLike.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1))) (skewAdjoint.{u1} R _inst_1 _inst_2)) R (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) R (AddSubgroup.setLike.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1))) (skewAdjoint.{u1} R _inst_1 _inst_2)) R (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) R (AddSubgroup.setLike.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1))) (skewAdjoint.{u1} R _inst_1 _inst_2)) R (coeSubtype.{succ u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) (SetLike.hasMem.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) R (AddSubgroup.setLike.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1))) x (skewAdjoint.{u1} R _inst_1 _inst_2)))))) x))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddCommGroup.{u1} R] [_inst_2 : StarAddMonoid.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)))] {x : Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) R (AddSubgroup.instSetLikeAddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1))) x (skewAdjoint.{u1} R _inst_1 _inst_2))}, Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1))) _inst_2)) (Subtype.val.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x (SetLike.coe.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) R (AddSubgroup.instSetLikeAddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) (skewAdjoint.{u1} R _inst_1 _inst_2))) x)) (Neg.neg.{u1} R (NegZeroClass.toNeg.{u1} R (SubNegZeroMonoid.toNegZeroClass.{u1} R (SubtractionMonoid.toSubNegZeroMonoid.{u1} R (SubtractionCommMonoid.toSubtractionMonoid.{u1} R (AddCommGroup.toDivisionAddCommMonoid.{u1} R _inst_1))))) (Subtype.val.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x (SetLike.coe.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) R (AddSubgroup.instSetLikeAddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) (skewAdjoint.{u1} R _inst_1 _inst_2))) x))
Case conversion may be inaccurate. Consider using '#align skew_adjoint.star_coe_eq skewAdjoint.star_val_eqₓ'. -/
@[simp, norm_cast]
theorem star_val_eq {x : skewAdjoint R} : star (x : R) = -x :=
  x.Prop
#align skew_adjoint.star_coe_eq skewAdjoint.star_val_eq

instance : Inhabited (skewAdjoint R) :=
  ⟨0⟩

/- warning: skew_adjoint.bit0_mem -> skewAdjoint.bit0_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddCommGroup.{u1} R] [_inst_2 : StarAddMonoid.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)))] {x : R}, (Membership.Mem.{u1, u1} R (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) (SetLike.hasMem.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) R (AddSubgroup.setLike.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1))) x (skewAdjoint.{u1} R _inst_1 _inst_2)) -> (Membership.Mem.{u1, u1} R (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) (SetLike.hasMem.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) R (AddSubgroup.setLike.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1))) (bit0.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1))))) x) (skewAdjoint.{u1} R _inst_1 _inst_2))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddCommGroup.{u1} R] [_inst_2 : StarAddMonoid.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)))] {x : R}, (Membership.mem.{u1, u1} R (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) R (AddSubgroup.instSetLikeAddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1))) x (skewAdjoint.{u1} R _inst_1 _inst_2)) -> (Membership.mem.{u1, u1} R (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1)) R (AddSubgroup.instSetLikeAddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1))) (bit0.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R _inst_1))))) x) (skewAdjoint.{u1} R _inst_1 _inst_2))
Case conversion may be inaccurate. Consider using '#align skew_adjoint.bit0_mem skewAdjoint.bit0_memₓ'. -/
theorem bit0_mem {x : R} (hx : x ∈ skewAdjoint R) : bit0 x ∈ skewAdjoint R := by
  rw [mem_iff, star_bit0, mem_iff.mp hx, bit0, bit0, neg_add]
#align skew_adjoint.bit0_mem skewAdjoint.bit0_mem

end AddGroup

section Ring

variable [Ring R] [StarRing R]

/- warning: skew_adjoint.conjugate -> skewAdjoint.conjugate is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1))] {x : R}, (Membership.Mem.{u1, u1} R (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (SetLike.hasMem.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) R (AddSubgroup.setLike.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) x (skewAdjoint.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1)) _inst_2))) -> (forall (z : R), Membership.Mem.{u1, u1} R (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (SetLike.hasMem.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) R (AddSubgroup.setLike.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1))) z x) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1)) _inst_2))) z)) (skewAdjoint.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1)) _inst_2)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : StarRing.{u1} R (Semiring.toNonUnitalSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))] {x : R}, (Membership.mem.{u1, u1} R (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (Ring.toAddCommGroup.{u1} R _inst_1))) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (Ring.toAddCommGroup.{u1} R _inst_1))) R (AddSubgroup.instSetLikeAddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (Ring.toAddCommGroup.{u1} R _inst_1)))) x (skewAdjoint.{u1} R (Ring.toAddCommGroup.{u1} R _inst_1) (StarRing.toStarAddMonoid.{u1} R (Semiring.toNonUnitalSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) _inst_2))) -> (forall (z : R), Membership.mem.{u1, u1} R (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (Ring.toAddCommGroup.{u1} R _inst_1))) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (Ring.toAddCommGroup.{u1} R _inst_1))) R (AddSubgroup.instSetLikeAddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (Ring.toAddCommGroup.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) z x) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) (StarRing.toStarAddMonoid.{u1} R (Semiring.toNonUnitalSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) _inst_2))) z)) (skewAdjoint.{u1} R (Ring.toAddCommGroup.{u1} R _inst_1) (StarRing.toStarAddMonoid.{u1} R (Semiring.toNonUnitalSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) _inst_2)))
Case conversion may be inaccurate. Consider using '#align skew_adjoint.conjugate skewAdjoint.conjugateₓ'. -/
theorem conjugate {x : R} (hx : x ∈ skewAdjoint R) (z : R) : z * x * star z ∈ skewAdjoint R := by
  simp only [mem_iff, star_mul, star_star, mem_iff.mp hx, neg_mul, mul_neg, mul_assoc]
#align skew_adjoint.conjugate skewAdjoint.conjugate

/- warning: skew_adjoint.conjugate' -> skewAdjoint.conjugate' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1))] {x : R}, (Membership.Mem.{u1, u1} R (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (SetLike.hasMem.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) R (AddSubgroup.setLike.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) x (skewAdjoint.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1)) _inst_2))) -> (forall (z : R), Membership.Mem.{u1, u1} R (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (SetLike.hasMem.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) R (AddSubgroup.setLike.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1))) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1)) _inst_2))) z) x) z) (skewAdjoint.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1)) _inst_2)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : StarRing.{u1} R (Semiring.toNonUnitalSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))] {x : R}, (Membership.mem.{u1, u1} R (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (Ring.toAddCommGroup.{u1} R _inst_1))) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (Ring.toAddCommGroup.{u1} R _inst_1))) R (AddSubgroup.instSetLikeAddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (Ring.toAddCommGroup.{u1} R _inst_1)))) x (skewAdjoint.{u1} R (Ring.toAddCommGroup.{u1} R _inst_1) (StarRing.toStarAddMonoid.{u1} R (Semiring.toNonUnitalSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) _inst_2))) -> (forall (z : R), Membership.mem.{u1, u1} R (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (Ring.toAddCommGroup.{u1} R _inst_1))) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (Ring.toAddCommGroup.{u1} R _inst_1))) R (AddSubgroup.instSetLikeAddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (Ring.toAddCommGroup.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) (StarRing.toStarAddMonoid.{u1} R (Semiring.toNonUnitalSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) _inst_2))) z) x) z) (skewAdjoint.{u1} R (Ring.toAddCommGroup.{u1} R _inst_1) (StarRing.toStarAddMonoid.{u1} R (Semiring.toNonUnitalSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) _inst_2)))
Case conversion may be inaccurate. Consider using '#align skew_adjoint.conjugate' skewAdjoint.conjugate'ₓ'. -/
theorem conjugate' {x : R} (hx : x ∈ skewAdjoint R) (z : R) : star z * x * z ∈ skewAdjoint R := by
  simp only [mem_iff, star_mul, star_star, mem_iff.mp hx, neg_mul, mul_neg, mul_assoc]
#align skew_adjoint.conjugate' skewAdjoint.conjugate'

/- warning: skew_adjoint.is_star_normal_of_mem -> skewAdjoint.isStarNormal_of_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1))] {x : R}, (Membership.Mem.{u1, u1} R (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (SetLike.hasMem.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) R (AddSubgroup.setLike.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) x (skewAdjoint.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1)) _inst_2))) -> (IsStarNormal.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1)) (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1)) _inst_2))) x)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : StarRing.{u1} R (Semiring.toNonUnitalSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))] {x : R}, (Membership.mem.{u1, u1} R (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (Ring.toAddCommGroup.{u1} R _inst_1))) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (Ring.toAddCommGroup.{u1} R _inst_1))) R (AddSubgroup.instSetLikeAddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (Ring.toAddCommGroup.{u1} R _inst_1)))) x (skewAdjoint.{u1} R (Ring.toAddCommGroup.{u1} R _inst_1) (StarRing.toStarAddMonoid.{u1} R (Semiring.toNonUnitalSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) _inst_2))) -> (IsStarNormal.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) (StarRing.toStarAddMonoid.{u1} R (Semiring.toNonUnitalSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) _inst_2))) x)
Case conversion may be inaccurate. Consider using '#align skew_adjoint.is_star_normal_of_mem skewAdjoint.isStarNormal_of_memₓ'. -/
theorem isStarNormal_of_mem {x : R} (hx : x ∈ skewAdjoint R) : IsStarNormal x :=
  ⟨by simp only [mem_iff] at hx; simp only [hx, Commute.neg_left]⟩
#align skew_adjoint.is_star_normal_of_mem skewAdjoint.isStarNormal_of_mem

instance (x : skewAdjoint R) : IsStarNormal (x : R) :=
  isStarNormal_of_mem (SetLike.coe_mem _)

end Ring

section SMul

variable [Star R] [TrivialStar R] [AddCommGroup A] [StarAddMonoid A]

/- warning: skew_adjoint.smul_mem -> skewAdjoint.smul_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Star.{u1} R] [_inst_2 : TrivialStar.{u1} R _inst_1] [_inst_3 : AddCommGroup.{u2} A] [_inst_4 : StarAddMonoid.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_3)))] [_inst_5 : Monoid.{u1} R] [_inst_6 : DistribMulAction.{u1, u2} R A _inst_5 (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_3)))] [_inst_7 : StarModule.{u1, u2} R A _inst_1 (InvolutiveStar.toHasStar.{u2} A (StarAddMonoid.toHasInvolutiveStar.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_3))) _inst_4)) (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_3))))) (DistribSMul.toSmulZeroClass.{u1, u2} R A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_3)))) (DistribMulAction.toDistribSMul.{u1, u2} R A _inst_5 (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_3))) _inst_6)))] (r : R) {x : A}, (Membership.Mem.{u2, u2} A (AddSubgroup.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_3)) (SetLike.hasMem.{u2, u2} (AddSubgroup.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_3)) A (AddSubgroup.setLike.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_3))) x (skewAdjoint.{u2} A _inst_3 _inst_4)) -> (Membership.Mem.{u2, u2} A (AddSubgroup.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_3)) (SetLike.hasMem.{u2, u2} (AddSubgroup.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_3)) A (AddSubgroup.setLike.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_3))) (SMul.smul.{u1, u2} R A (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_3))))) (DistribSMul.toSmulZeroClass.{u1, u2} R A (AddMonoid.toAddZeroClass.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_3)))) (DistribMulAction.toDistribSMul.{u1, u2} R A _inst_5 (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_3))) _inst_6))) r x) (skewAdjoint.{u2} A _inst_3 _inst_4))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : Star.{u2} R] [_inst_2 : TrivialStar.{u2} R _inst_1] [_inst_3 : AddCommGroup.{u1} A] [_inst_4 : StarAddMonoid.{u1} A (SubNegMonoid.toAddMonoid.{u1} A (AddGroup.toSubNegMonoid.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_3)))] [_inst_5 : Monoid.{u2} R] [_inst_6 : DistribMulAction.{u2, u1} R A _inst_5 (SubNegMonoid.toAddMonoid.{u1} A (AddGroup.toSubNegMonoid.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_3)))] [_inst_7 : StarModule.{u2, u1} R A _inst_1 (InvolutiveStar.toStar.{u1} A (StarAddMonoid.toInvolutiveStar.{u1} A (SubNegMonoid.toAddMonoid.{u1} A (AddGroup.toSubNegMonoid.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_3))) _inst_4)) (SMulZeroClass.toSMul.{u2, u1} R A (NegZeroClass.toZero.{u1} A (SubNegZeroMonoid.toNegZeroClass.{u1} A (SubtractionMonoid.toSubNegZeroMonoid.{u1} A (SubtractionCommMonoid.toSubtractionMonoid.{u1} A (AddCommGroup.toDivisionAddCommMonoid.{u1} A _inst_3))))) (DistribSMul.toSMulZeroClass.{u2, u1} R A (AddMonoid.toAddZeroClass.{u1} A (SubNegMonoid.toAddMonoid.{u1} A (AddGroup.toSubNegMonoid.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_3)))) (DistribMulAction.toDistribSMul.{u2, u1} R A _inst_5 (SubNegMonoid.toAddMonoid.{u1} A (AddGroup.toSubNegMonoid.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_3))) _inst_6)))] (r : R) {x : A}, (Membership.mem.{u1, u1} A (AddSubgroup.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_3)) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_3)) A (AddSubgroup.instSetLikeAddSubgroup.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_3))) x (skewAdjoint.{u1} A _inst_3 _inst_4)) -> (Membership.mem.{u1, u1} A (AddSubgroup.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_3)) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_3)) A (AddSubgroup.instSetLikeAddSubgroup.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_3))) (HSMul.hSMul.{u2, u1, u1} R A A (instHSMul.{u2, u1} R A (SMulZeroClass.toSMul.{u2, u1} R A (NegZeroClass.toZero.{u1} A (SubNegZeroMonoid.toNegZeroClass.{u1} A (SubtractionMonoid.toSubNegZeroMonoid.{u1} A (SubtractionCommMonoid.toSubtractionMonoid.{u1} A (AddCommGroup.toDivisionAddCommMonoid.{u1} A _inst_3))))) (DistribSMul.toSMulZeroClass.{u2, u1} R A (AddMonoid.toAddZeroClass.{u1} A (SubNegMonoid.toAddMonoid.{u1} A (AddGroup.toSubNegMonoid.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_3)))) (DistribMulAction.toDistribSMul.{u2, u1} R A _inst_5 (SubNegMonoid.toAddMonoid.{u1} A (AddGroup.toSubNegMonoid.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_3))) _inst_6)))) r x) (skewAdjoint.{u1} A _inst_3 _inst_4))
Case conversion may be inaccurate. Consider using '#align skew_adjoint.smul_mem skewAdjoint.smul_memₓ'. -/
theorem smul_mem [Monoid R] [DistribMulAction R A] [StarModule R A] (r : R) {x : A}
    (h : x ∈ skewAdjoint A) : r • x ∈ skewAdjoint A := by
  rw [mem_iff, star_smul, star_trivial, mem_iff.mp h, smul_neg r]
#align skew_adjoint.smul_mem skewAdjoint.smul_mem

instance [Monoid R] [DistribMulAction R A] [StarModule R A] : SMul R (skewAdjoint A) :=
  ⟨fun r x => ⟨r • x, smul_mem r x.Prop⟩⟩

/- warning: skew_adjoint.coe_smul -> skewAdjoint.val_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align skew_adjoint.coe_smul skewAdjoint.val_smulₓ'. -/
@[simp, norm_cast]
theorem val_smul [Monoid R] [DistribMulAction R A] [StarModule R A] (r : R) (x : skewAdjoint A) :
    ↑(r • x) = r • (x : A) :=
  rfl
#align skew_adjoint.coe_smul skewAdjoint.val_smul

instance [Monoid R] [DistribMulAction R A] [StarModule R A] : DistribMulAction R (skewAdjoint A) :=
  Function.Injective.distribMulAction (skewAdjoint A).Subtype Subtype.coe_injective val_smul

instance [Semiring R] [Module R A] [StarModule R A] : Module R (skewAdjoint A) :=
  Function.Injective.module R (skewAdjoint A).Subtype Subtype.coe_injective val_smul

end SMul

end skewAdjoint

/- warning: is_self_adjoint.smul_mem_skew_adjoint -> IsSelfAdjoint.smul_mem_skewAdjoint is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} A] [_inst_3 : Module.{u1, u2} R A (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} A _inst_2)] [_inst_4 : StarAddMonoid.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))] [_inst_5 : StarAddMonoid.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_2)))] [_inst_6 : StarModule.{u1, u2} R A (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) _inst_4)) (InvolutiveStar.toHasStar.{u2} A (StarAddMonoid.toHasInvolutiveStar.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_2))) _inst_5)) (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (AddCommGroup.toAddCommMonoid.{u2} A _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (AddCommGroup.toAddCommMonoid.{u2} A _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (AddCommGroup.toAddCommMonoid.{u2} A _inst_2)))) (Module.toMulActionWithZero.{u1, u2} R A (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} A _inst_2) _inst_3))))] {r : R}, (Membership.Mem.{u1, u1} R (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (SetLike.hasMem.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) R (AddSubgroup.setLike.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) r (skewAdjoint.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_4)) -> (forall {a : A}, (IsSelfAdjoint.{u2} A (InvolutiveStar.toHasStar.{u2} A (StarAddMonoid.toHasInvolutiveStar.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_2))) _inst_5)) a) -> (Membership.Mem.{u2, u2} A (AddSubgroup.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_2)) (SetLike.hasMem.{u2, u2} (AddSubgroup.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_2)) A (AddSubgroup.setLike.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_2))) (SMul.smul.{u1, u2} R A (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (AddCommGroup.toAddCommMonoid.{u2} A _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (AddCommGroup.toAddCommMonoid.{u2} A _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (AddCommGroup.toAddCommMonoid.{u2} A _inst_2)))) (Module.toMulActionWithZero.{u1, u2} R A (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} A _inst_2) _inst_3)))) r a) (skewAdjoint.{u2} A _inst_2 _inst_5)))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : Ring.{u2} R] [_inst_2 : AddCommGroup.{u1} A] [_inst_3 : Module.{u2, u1} R A (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} A _inst_2)] [_inst_4 : StarAddMonoid.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddGroupWithOne.toAddMonoidWithOne.{u2} R (Ring.toAddGroupWithOne.{u2} R _inst_1)))] [_inst_5 : StarAddMonoid.{u1} A (SubNegMonoid.toAddMonoid.{u1} A (AddGroup.toSubNegMonoid.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_2)))] [_inst_6 : StarModule.{u2, u1} R A (InvolutiveStar.toStar.{u2} R (StarAddMonoid.toInvolutiveStar.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddGroupWithOne.toAddMonoidWithOne.{u2} R (Ring.toAddGroupWithOne.{u2} R _inst_1))) _inst_4)) (InvolutiveStar.toStar.{u1} A (StarAddMonoid.toInvolutiveStar.{u1} A (SubNegMonoid.toAddMonoid.{u1} A (AddGroup.toSubNegMonoid.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_2))) _inst_5)) (SMulZeroClass.toSMul.{u2, u1} R A (NegZeroClass.toZero.{u1} A (SubNegZeroMonoid.toNegZeroClass.{u1} A (SubtractionMonoid.toSubNegZeroMonoid.{u1} A (SubtractionCommMonoid.toSubtractionMonoid.{u1} A (AddCommGroup.toDivisionAddCommMonoid.{u1} A _inst_2))))) (SMulWithZero.toSMulZeroClass.{u2, u1} R A (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (NegZeroClass.toZero.{u1} A (SubNegZeroMonoid.toNegZeroClass.{u1} A (SubtractionMonoid.toSubNegZeroMonoid.{u1} A (SubtractionCommMonoid.toSubtractionMonoid.{u1} A (AddCommGroup.toDivisionAddCommMonoid.{u1} A _inst_2))))) (MulActionWithZero.toSMulWithZero.{u2, u1} R A (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1)) (NegZeroClass.toZero.{u1} A (SubNegZeroMonoid.toNegZeroClass.{u1} A (SubtractionMonoid.toSubNegZeroMonoid.{u1} A (SubtractionCommMonoid.toSubtractionMonoid.{u1} A (AddCommGroup.toDivisionAddCommMonoid.{u1} A _inst_2))))) (Module.toMulActionWithZero.{u2, u1} R A (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} A _inst_2) _inst_3))))] {r : R}, (Membership.mem.{u2, u2} R (AddSubgroup.{u2} R (AddCommGroup.toAddGroup.{u2} R (Ring.toAddCommGroup.{u2} R _inst_1))) (SetLike.instMembership.{u2, u2} (AddSubgroup.{u2} R (AddCommGroup.toAddGroup.{u2} R (Ring.toAddCommGroup.{u2} R _inst_1))) R (AddSubgroup.instSetLikeAddSubgroup.{u2} R (AddCommGroup.toAddGroup.{u2} R (Ring.toAddCommGroup.{u2} R _inst_1)))) r (skewAdjoint.{u2} R (Ring.toAddCommGroup.{u2} R _inst_1) _inst_4)) -> (forall {a : A}, (IsSelfAdjoint.{u1} A (InvolutiveStar.toStar.{u1} A (StarAddMonoid.toInvolutiveStar.{u1} A (SubNegMonoid.toAddMonoid.{u1} A (AddGroup.toSubNegMonoid.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_2))) _inst_5)) a) -> (Membership.mem.{u1, u1} A (AddSubgroup.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_2)) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_2)) A (AddSubgroup.instSetLikeAddSubgroup.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_2))) (HSMul.hSMul.{u2, u1, u1} R A A (instHSMul.{u2, u1} R A (SMulZeroClass.toSMul.{u2, u1} R A (NegZeroClass.toZero.{u1} A (SubNegZeroMonoid.toNegZeroClass.{u1} A (SubtractionMonoid.toSubNegZeroMonoid.{u1} A (SubtractionCommMonoid.toSubtractionMonoid.{u1} A (AddCommGroup.toDivisionAddCommMonoid.{u1} A _inst_2))))) (SMulWithZero.toSMulZeroClass.{u2, u1} R A (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (NegZeroClass.toZero.{u1} A (SubNegZeroMonoid.toNegZeroClass.{u1} A (SubtractionMonoid.toSubNegZeroMonoid.{u1} A (SubtractionCommMonoid.toSubtractionMonoid.{u1} A (AddCommGroup.toDivisionAddCommMonoid.{u1} A _inst_2))))) (MulActionWithZero.toSMulWithZero.{u2, u1} R A (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1)) (NegZeroClass.toZero.{u1} A (SubNegZeroMonoid.toNegZeroClass.{u1} A (SubtractionMonoid.toSubNegZeroMonoid.{u1} A (SubtractionCommMonoid.toSubtractionMonoid.{u1} A (AddCommGroup.toDivisionAddCommMonoid.{u1} A _inst_2))))) (Module.toMulActionWithZero.{u2, u1} R A (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} A _inst_2) _inst_3))))) r a) (skewAdjoint.{u1} A _inst_2 _inst_5)))
Case conversion may be inaccurate. Consider using '#align is_self_adjoint.smul_mem_skew_adjoint IsSelfAdjoint.smul_mem_skewAdjointₓ'. -/
/-- Scalar multiplication of a self-adjoint element by a skew-adjoint element produces a
skew-adjoint element. -/
theorem IsSelfAdjoint.smul_mem_skewAdjoint [Ring R] [AddCommGroup A] [Module R A] [StarAddMonoid R]
    [StarAddMonoid A] [StarModule R A] {r : R} (hr : r ∈ skewAdjoint R) {a : A}
    (ha : IsSelfAdjoint a) : r • a ∈ skewAdjoint A :=
  (star_smul _ _).trans <| (congr_arg₂ _ hr ha).trans <| neg_smul _ _
#align is_self_adjoint.smul_mem_skew_adjoint IsSelfAdjoint.smul_mem_skewAdjoint

/- warning: is_self_adjoint_smul_of_mem_skew_adjoint -> isSelfAdjoint_smul_of_mem_skewAdjoint is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} A] [_inst_3 : Module.{u1, u2} R A (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} A _inst_2)] [_inst_4 : StarAddMonoid.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))] [_inst_5 : StarAddMonoid.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_2)))] [_inst_6 : StarModule.{u1, u2} R A (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) _inst_4)) (InvolutiveStar.toHasStar.{u2} A (StarAddMonoid.toHasInvolutiveStar.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_2))) _inst_5)) (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (AddCommGroup.toAddCommMonoid.{u2} A _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (AddCommGroup.toAddCommMonoid.{u2} A _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (AddCommGroup.toAddCommMonoid.{u2} A _inst_2)))) (Module.toMulActionWithZero.{u1, u2} R A (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} A _inst_2) _inst_3))))] {r : R}, (Membership.Mem.{u1, u1} R (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (SetLike.hasMem.{u1, u1} (AddSubgroup.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) R (AddSubgroup.setLike.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) r (skewAdjoint.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_4)) -> (forall {a : A}, (Membership.Mem.{u2, u2} A (AddSubgroup.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_2)) (SetLike.hasMem.{u2, u2} (AddSubgroup.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_2)) A (AddSubgroup.setLike.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_2))) a (skewAdjoint.{u2} A _inst_2 _inst_5)) -> (IsSelfAdjoint.{u2} A (InvolutiveStar.toHasStar.{u2} A (StarAddMonoid.toHasInvolutiveStar.{u2} A (SubNegMonoid.toAddMonoid.{u2} A (AddGroup.toSubNegMonoid.{u2} A (AddCommGroup.toAddGroup.{u2} A _inst_2))) _inst_5)) (SMul.smul.{u1, u2} R A (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (AddCommGroup.toAddCommMonoid.{u2} A _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (AddCommGroup.toAddCommMonoid.{u2} A _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (AddCommGroup.toAddCommMonoid.{u2} A _inst_2)))) (Module.toMulActionWithZero.{u1, u2} R A (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} A _inst_2) _inst_3)))) r a)))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : Ring.{u2} R] [_inst_2 : AddCommGroup.{u1} A] [_inst_3 : Module.{u2, u1} R A (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} A _inst_2)] [_inst_4 : StarAddMonoid.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddGroupWithOne.toAddMonoidWithOne.{u2} R (Ring.toAddGroupWithOne.{u2} R _inst_1)))] [_inst_5 : StarAddMonoid.{u1} A (SubNegMonoid.toAddMonoid.{u1} A (AddGroup.toSubNegMonoid.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_2)))] [_inst_6 : StarModule.{u2, u1} R A (InvolutiveStar.toStar.{u2} R (StarAddMonoid.toInvolutiveStar.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddGroupWithOne.toAddMonoidWithOne.{u2} R (Ring.toAddGroupWithOne.{u2} R _inst_1))) _inst_4)) (InvolutiveStar.toStar.{u1} A (StarAddMonoid.toInvolutiveStar.{u1} A (SubNegMonoid.toAddMonoid.{u1} A (AddGroup.toSubNegMonoid.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_2))) _inst_5)) (SMulZeroClass.toSMul.{u2, u1} R A (NegZeroClass.toZero.{u1} A (SubNegZeroMonoid.toNegZeroClass.{u1} A (SubtractionMonoid.toSubNegZeroMonoid.{u1} A (SubtractionCommMonoid.toSubtractionMonoid.{u1} A (AddCommGroup.toDivisionAddCommMonoid.{u1} A _inst_2))))) (SMulWithZero.toSMulZeroClass.{u2, u1} R A (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (NegZeroClass.toZero.{u1} A (SubNegZeroMonoid.toNegZeroClass.{u1} A (SubtractionMonoid.toSubNegZeroMonoid.{u1} A (SubtractionCommMonoid.toSubtractionMonoid.{u1} A (AddCommGroup.toDivisionAddCommMonoid.{u1} A _inst_2))))) (MulActionWithZero.toSMulWithZero.{u2, u1} R A (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1)) (NegZeroClass.toZero.{u1} A (SubNegZeroMonoid.toNegZeroClass.{u1} A (SubtractionMonoid.toSubNegZeroMonoid.{u1} A (SubtractionCommMonoid.toSubtractionMonoid.{u1} A (AddCommGroup.toDivisionAddCommMonoid.{u1} A _inst_2))))) (Module.toMulActionWithZero.{u2, u1} R A (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} A _inst_2) _inst_3))))] {r : R}, (Membership.mem.{u2, u2} R (AddSubgroup.{u2} R (AddCommGroup.toAddGroup.{u2} R (Ring.toAddCommGroup.{u2} R _inst_1))) (SetLike.instMembership.{u2, u2} (AddSubgroup.{u2} R (AddCommGroup.toAddGroup.{u2} R (Ring.toAddCommGroup.{u2} R _inst_1))) R (AddSubgroup.instSetLikeAddSubgroup.{u2} R (AddCommGroup.toAddGroup.{u2} R (Ring.toAddCommGroup.{u2} R _inst_1)))) r (skewAdjoint.{u2} R (Ring.toAddCommGroup.{u2} R _inst_1) _inst_4)) -> (forall {a : A}, (Membership.mem.{u1, u1} A (AddSubgroup.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_2)) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_2)) A (AddSubgroup.instSetLikeAddSubgroup.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_2))) a (skewAdjoint.{u1} A _inst_2 _inst_5)) -> (IsSelfAdjoint.{u1} A (InvolutiveStar.toStar.{u1} A (StarAddMonoid.toInvolutiveStar.{u1} A (SubNegMonoid.toAddMonoid.{u1} A (AddGroup.toSubNegMonoid.{u1} A (AddCommGroup.toAddGroup.{u1} A _inst_2))) _inst_5)) (HSMul.hSMul.{u2, u1, u1} R A A (instHSMul.{u2, u1} R A (SMulZeroClass.toSMul.{u2, u1} R A (NegZeroClass.toZero.{u1} A (SubNegZeroMonoid.toNegZeroClass.{u1} A (SubtractionMonoid.toSubNegZeroMonoid.{u1} A (SubtractionCommMonoid.toSubtractionMonoid.{u1} A (AddCommGroup.toDivisionAddCommMonoid.{u1} A _inst_2))))) (SMulWithZero.toSMulZeroClass.{u2, u1} R A (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (NegZeroClass.toZero.{u1} A (SubNegZeroMonoid.toNegZeroClass.{u1} A (SubtractionMonoid.toSubNegZeroMonoid.{u1} A (SubtractionCommMonoid.toSubtractionMonoid.{u1} A (AddCommGroup.toDivisionAddCommMonoid.{u1} A _inst_2))))) (MulActionWithZero.toSMulWithZero.{u2, u1} R A (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1)) (NegZeroClass.toZero.{u1} A (SubNegZeroMonoid.toNegZeroClass.{u1} A (SubtractionMonoid.toSubNegZeroMonoid.{u1} A (SubtractionCommMonoid.toSubtractionMonoid.{u1} A (AddCommGroup.toDivisionAddCommMonoid.{u1} A _inst_2))))) (Module.toMulActionWithZero.{u2, u1} R A (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} A _inst_2) _inst_3))))) r a)))
Case conversion may be inaccurate. Consider using '#align is_self_adjoint_smul_of_mem_skew_adjoint isSelfAdjoint_smul_of_mem_skewAdjointₓ'. -/
/-- Scalar multiplication of a skew-adjoint element by a skew-adjoint element produces a
self-adjoint element. -/
theorem isSelfAdjoint_smul_of_mem_skewAdjoint [Ring R] [AddCommGroup A] [Module R A]
    [StarAddMonoid R] [StarAddMonoid A] [StarModule R A] {r : R} (hr : r ∈ skewAdjoint R) {a : A}
    (ha : a ∈ skewAdjoint A) : IsSelfAdjoint (r • a) :=
  (star_smul _ _).trans <| (congr_arg₂ _ hr ha).trans <| neg_smul_neg _ _
#align is_self_adjoint_smul_of_mem_skew_adjoint isSelfAdjoint_smul_of_mem_skewAdjoint

/- warning: is_star_normal_zero -> isStarNormal_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] [_inst_2 : StarRing.{u1} R (Semiring.toNonUnitalSemiring.{u1} R _inst_1)], IsStarNormal.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonUnitalSemiring.{u1} R _inst_1)))) (StarRing.toStarAddMonoid.{u1} R (Semiring.toNonUnitalSemiring.{u1} R _inst_1) _inst_2))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] [_inst_2 : StarRing.{u1} R (Semiring.toNonUnitalSemiring.{u1} R _inst_1)], IsStarNormal.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (StarRing.toStarAddMonoid.{u1} R (Semiring.toNonUnitalSemiring.{u1} R _inst_1) _inst_2))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align is_star_normal_zero isStarNormal_zeroₓ'. -/
instance isStarNormal_zero [Semiring R] [StarRing R] : IsStarNormal (0 : R) :=
  ⟨by simp only [star_comm_self, star_zero]⟩
#align is_star_normal_zero isStarNormal_zero

/- warning: is_star_normal_one -> isStarNormal_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Monoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R _inst_1)], IsStarNormal.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (MulOneClass.toHasOne.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Monoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R _inst_1)], IsStarNormal.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Monoid.toOne.{u1} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align is_star_normal_one isStarNormal_oneₓ'. -/
instance isStarNormal_one [Monoid R] [StarSemigroup R] : IsStarNormal (1 : R) :=
  ⟨by simp only [star_comm_self, star_one]⟩
#align is_star_normal_one isStarNormal_one

/- warning: is_star_normal_star_self -> isStarNormal_star_self is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Monoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R _inst_1)] {x : R} [_inst_3 : IsStarNormal.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) x], IsStarNormal.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) x)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Monoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R _inst_1)] {x : R} [_inst_3 : IsStarNormal.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) x], IsStarNormal.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) x)
Case conversion may be inaccurate. Consider using '#align is_star_normal_star_self isStarNormal_star_selfₓ'. -/
instance isStarNormal_star_self [Monoid R] [StarSemigroup R] {x : R} [IsStarNormal x] :
    IsStarNormal (star x) :=
  ⟨show star (star x) * star x = star x * star (star x) by rw [star_star, star_comm_self']⟩
#align is_star_normal_star_self isStarNormal_star_self

/- warning: has_trivial_star.is_star_normal -> TrivialStar.isStarNormal is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Monoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R _inst_1)] [_inst_3 : TrivialStar.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2))] {x : R}, IsStarNormal.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) x
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Monoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R _inst_1)] [_inst_3 : TrivialStar.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2))] {x : R}, IsStarNormal.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) x
Case conversion may be inaccurate. Consider using '#align has_trivial_star.is_star_normal TrivialStar.isStarNormalₓ'. -/
-- see Note [lower instance priority]
instance (priority := 100) TrivialStar.isStarNormal [Monoid R] [StarSemigroup R] [TrivialStar R]
    {x : R} : IsStarNormal x :=
  ⟨by rw [star_trivial]⟩
#align has_trivial_star.is_star_normal TrivialStar.isStarNormal

/- warning: comm_monoid.is_star_normal -> CommMonoid.isStarNormal is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))] {x : R}, IsStarNormal.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))) (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) _inst_2)) x
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))] {x : R}, IsStarNormal.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))) (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) _inst_2)) x
Case conversion may be inaccurate. Consider using '#align comm_monoid.is_star_normal CommMonoid.isStarNormalₓ'. -/
-- see Note [lower instance priority]
instance (priority := 100) CommMonoid.isStarNormal [CommMonoid R] [StarSemigroup R] {x : R} :
    IsStarNormal x :=
  ⟨mul_comm _ _⟩
#align comm_monoid.is_star_normal CommMonoid.isStarNormal

