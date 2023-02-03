/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.star.basic
! leanprover-community/mathlib commit 2705404e701abc6b3127da906f40bae062a169c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Ring.Aut
import Mathbin.Algebra.Ring.CompTypeclasses
import Mathbin.Data.Rat.Cast
import Mathbin.GroupTheory.GroupAction.Opposite
import Mathbin.Data.SetLike.Basic

/-!
# Star monoids, rings, and modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We introduce the basic algebraic notions of star monoids, star rings, and star modules.
A star algebra is simply a star ring that is also a star module.

These are implemented as "mixin" typeclasses, so to summon a star ring (for example)
one needs to write `(R : Type) [ring R] [star_ring R]`.
This avoids difficulties with diamond inheritance.

We also define the class `star_ordered_ring R`, which says that the order on `R` respects the
star operation, i.e. an element `r` is nonnegative iff there exists an `s` such that
`r = star s * s`.

For now we simply do not introduce notations,
as different users are expected to feel strongly about the relative merits of
`r^*`, `r†`, `rᘁ`, and so on.

Our star rings are actually star semirings, but of course we can prove
`star_neg : star (-r) = - star r` when the underlying semiring is a ring.

## TODO

* In a Banach star algebra without a well-defined square root, the natural ordering is given by the
positive cone which is the closure of the sums of elements `star r * r`. A weaker version of
`star_ordered_ring` could be defined for this case. Note that the current definition has the
advantage of not requiring a topology.
-/


assert_not_exists Finset

assert_not_exists Subgroup

universe u v

open MulOpposite

#print Star /-
/-- Notation typeclass (with no default notation!) for an algebraic structure with a star operation.
-/
class Star (R : Type u) where
  unit : R → R
#align has_star Star
-/

variable {R : Type u}

export Star (unit)

/-- A star operation (e.g. complex conjugate).
-/
add_decl_doc star

#print StarMemClass /-
/-- `star_mem_class S G` states `S` is a type of subsets `s ⊆ G` closed under star. -/
class StarMemClass (S R : Type _) [Star R] [SetLike S R] where
  star_mem : ∀ {s : S} {r : R}, r ∈ s → star r ∈ s
#align star_mem_class StarMemClass
-/

export StarMemClass (star_mem)

namespace StarMemClass

variable {S : Type u} [Star R] [SetLike S R] [hS : StarMemClass S R] (s : S)

include hS

instance : Star s where unit r := ⟨star (r : R), star_mem r.Prop⟩

end StarMemClass

#print InvolutiveStar /-
/-- Typeclass for a star operation with is involutive.
-/
class InvolutiveStar (R : Type u) extends Star R where
  star_involutive : Function.Involutive star
#align has_involutive_star InvolutiveStar
-/

export InvolutiveStar (star_involutive)

#print star_star /-
@[simp]
theorem star_star [InvolutiveStar R] (r : R) : star (star r) = r :=
  star_involutive _
#align star_star star_star
-/

#print star_injective /-
theorem star_injective [InvolutiveStar R] : Function.Injective (star : R → R) :=
  star_involutive.Injective
#align star_injective star_injective
-/

#print Equiv.star /-
/-- `star` as an equivalence when it is involutive. -/
protected def Equiv.star [InvolutiveStar R] : Equiv.Perm R :=
  star_involutive.toPerm _
#align equiv.star Equiv.star
-/

#print eq_star_of_eq_star /-
theorem eq_star_of_eq_star [InvolutiveStar R] {r s : R} (h : r = star s) : s = star r := by simp [h]
#align eq_star_of_eq_star eq_star_of_eq_star
-/

#print eq_star_iff_eq_star /-
theorem eq_star_iff_eq_star [InvolutiveStar R] {r s : R} : r = star s ↔ s = star r :=
  ⟨eq_star_of_eq_star, eq_star_of_eq_star⟩
#align eq_star_iff_eq_star eq_star_iff_eq_star
-/

#print star_eq_iff_star_eq /-
theorem star_eq_iff_star_eq [InvolutiveStar R] {r s : R} : star r = s ↔ star s = r :=
  eq_comm.trans <| eq_star_iff_eq_star.trans eq_comm
#align star_eq_iff_star_eq star_eq_iff_star_eq
-/

#print TrivialStar /-
/-- Typeclass for a trivial star operation. This is mostly meant for `ℝ`.
-/
class TrivialStar (R : Type u) [Star R] : Prop where
  star_trivial : ∀ r : R, star r = r
#align has_trivial_star TrivialStar
-/

export TrivialStar (star_trivial)

attribute [simp] star_trivial

#print StarSemigroup /-
/-- A `*`-semigroup is a semigroup `R` with an involutive operations `star`
so `star (r * s) = star s * star r`.
-/
class StarSemigroup (R : Type u) [Semigroup R] extends InvolutiveStar R where
  star_mul : ∀ r s : R, star (r * s) = star s * star r
#align star_semigroup StarSemigroup
-/

export StarSemigroup (star_mul)

attribute [simp] star_mul

/- warning: star_mul' -> star_mul' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemigroup.{u1} R] [_inst_2 : StarSemigroup.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1)] (x : R) (y : R), Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1) _inst_2)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Semigroup.toHasMul.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1))) x y)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Semigroup.toHasMul.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1))) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1) _inst_2)) x) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1) _inst_2)) y))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemigroup.{u1} R] [_inst_2 : StarSemigroup.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1)] (x : R) (y : R), Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1) _inst_2)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Semigroup.toMul.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1))) x y)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Semigroup.toMul.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1))) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1) _inst_2)) x) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1) _inst_2)) y))
Case conversion may be inaccurate. Consider using '#align star_mul' star_mul'ₓ'. -/
/-- In a commutative ring, make `simp` prefer leaving the order unchanged. -/
@[simp]
theorem star_mul' [CommSemigroup R] [StarSemigroup R] (x y : R) : star (x * y) = star x * star y :=
  (star_mul x y).trans (mul_comm _ _)
#align star_mul' star_mul'

/- warning: star_mul_equiv -> starMulEquiv is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semigroup.{u1} R] [_inst_2 : StarSemigroup.{u1} R _inst_1], MulEquiv.{u1, u1} R (MulOpposite.{u1} R) (Semigroup.toHasMul.{u1} R _inst_1) (MulOpposite.hasMul.{u1} R (Semigroup.toHasMul.{u1} R _inst_1))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semigroup.{u1} R] [_inst_2 : StarSemigroup.{u1} R _inst_1], MulEquiv.{u1, u1} R (MulOpposite.{u1} R) (Semigroup.toMul.{u1} R _inst_1) (MulOpposite.instMulMulOpposite.{u1} R (Semigroup.toMul.{u1} R _inst_1))
Case conversion may be inaccurate. Consider using '#align star_mul_equiv starMulEquivₓ'. -/
/-- `star` as an `mul_equiv` from `R` to `Rᵐᵒᵖ` -/
@[simps apply]
def starMulEquiv [Semigroup R] [StarSemigroup R] : R ≃* Rᵐᵒᵖ :=
  {
    (InvolutiveStar.star_involutive.toPerm star).trans
      opEquiv with
    toFun := fun x => MulOpposite.op (star x)
    map_mul' := fun x y => (star_mul x y).symm ▸ MulOpposite.op_mul _ _ }
#align star_mul_equiv starMulEquiv

/- warning: star_mul_aut -> starMulAut is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemigroup.{u1} R] [_inst_2 : StarSemigroup.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1)], MulAut.{u1} R (Semigroup.toHasMul.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemigroup.{u1} R] [_inst_2 : StarSemigroup.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1)], MulAut.{u1} R (Semigroup.toMul.{u1} R (CommSemigroup.toSemigroup.{u1} R _inst_1))
Case conversion may be inaccurate. Consider using '#align star_mul_aut starMulAutₓ'. -/
/-- `star` as a `mul_aut` for commutative `R`. -/
@[simps apply]
def starMulAut [CommSemigroup R] [StarSemigroup R] : MulAut R :=
  {
    InvolutiveStar.star_involutive.toPerm
      star with
    toFun := star
    map_mul' := star_mul' }
#align star_mul_aut starMulAut

variable (R)

/- warning: star_one -> star_one is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Monoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R _inst_1)], Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (MulOneClass.toHasOne.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (MulOneClass.toHasOne.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)))))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : Monoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R _inst_1)], Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Monoid.toOne.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Monoid.toOne.{u1} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align star_one star_oneₓ'. -/
@[simp]
theorem star_one [Monoid R] [StarSemigroup R] : star (1 : R) = 1 :=
  op_injective <| (starMulEquiv : R ≃* Rᵐᵒᵖ).map_one.trans (op_one _).symm
#align star_one star_one

variable {R}

#print star_pow /-
@[simp]
theorem star_pow [Monoid R] [StarSemigroup R] (x : R) (n : ℕ) : star (x ^ n) = star x ^ n :=
  op_injective <|
    ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_pow x n).trans (op_pow (star x) n).symm
#align star_pow star_pow
-/

/- warning: star_inv -> star_inv is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Group.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R (DivInvMonoid.toMonoid.{u1} R (Group.toDivInvMonoid.{u1} R _inst_1)))] (x : R), Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R (DivInvMonoid.toMonoid.{u1} R (Group.toDivInvMonoid.{u1} R _inst_1))) _inst_2)) (Inv.inv.{u1} R (DivInvMonoid.toHasInv.{u1} R (Group.toDivInvMonoid.{u1} R _inst_1)) x)) (Inv.inv.{u1} R (DivInvMonoid.toHasInv.{u1} R (Group.toDivInvMonoid.{u1} R _inst_1)) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R (DivInvMonoid.toMonoid.{u1} R (Group.toDivInvMonoid.{u1} R _inst_1))) _inst_2)) x))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Group.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R (DivInvMonoid.toMonoid.{u1} R (Group.toDivInvMonoid.{u1} R _inst_1)))] (x : R), Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R (DivInvMonoid.toMonoid.{u1} R (Group.toDivInvMonoid.{u1} R _inst_1))) _inst_2)) (Inv.inv.{u1} R (InvOneClass.toInv.{u1} R (DivInvOneMonoid.toInvOneClass.{u1} R (DivisionMonoid.toDivInvOneMonoid.{u1} R (Group.toDivisionMonoid.{u1} R _inst_1)))) x)) (Inv.inv.{u1} R (InvOneClass.toInv.{u1} R (DivInvOneMonoid.toInvOneClass.{u1} R (DivisionMonoid.toDivInvOneMonoid.{u1} R (Group.toDivisionMonoid.{u1} R _inst_1)))) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R (DivInvMonoid.toMonoid.{u1} R (Group.toDivInvMonoid.{u1} R _inst_1))) _inst_2)) x))
Case conversion may be inaccurate. Consider using '#align star_inv star_invₓ'. -/
@[simp]
theorem star_inv [Group R] [StarSemigroup R] (x : R) : star x⁻¹ = (star x)⁻¹ :=
  op_injective <| ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_inv x).trans (op_inv (star x)).symm
#align star_inv star_inv

#print star_zpow /-
@[simp]
theorem star_zpow [Group R] [StarSemigroup R] (x : R) (z : ℤ) : star (x ^ z) = star x ^ z :=
  op_injective <|
    ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_zpow x z).trans (op_zpow (star x) z).symm
#align star_zpow star_zpow
-/

/- warning: star_div -> star_div is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommGroup.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R (DivInvMonoid.toMonoid.{u1} R (Group.toDivInvMonoid.{u1} R (CommGroup.toGroup.{u1} R _inst_1))))] (x : R) (y : R), Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R (DivInvMonoid.toMonoid.{u1} R (Group.toDivInvMonoid.{u1} R (CommGroup.toGroup.{u1} R _inst_1)))) _inst_2)) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (DivInvMonoid.toHasDiv.{u1} R (Group.toDivInvMonoid.{u1} R (CommGroup.toGroup.{u1} R _inst_1)))) x y)) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (DivInvMonoid.toHasDiv.{u1} R (Group.toDivInvMonoid.{u1} R (CommGroup.toGroup.{u1} R _inst_1)))) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R (DivInvMonoid.toMonoid.{u1} R (Group.toDivInvMonoid.{u1} R (CommGroup.toGroup.{u1} R _inst_1)))) _inst_2)) x) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R (DivInvMonoid.toMonoid.{u1} R (Group.toDivInvMonoid.{u1} R (CommGroup.toGroup.{u1} R _inst_1)))) _inst_2)) y))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommGroup.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R (DivInvMonoid.toMonoid.{u1} R (Group.toDivInvMonoid.{u1} R (CommGroup.toGroup.{u1} R _inst_1))))] (x : R) (y : R), Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R (DivInvMonoid.toMonoid.{u1} R (Group.toDivInvMonoid.{u1} R (CommGroup.toGroup.{u1} R _inst_1)))) _inst_2)) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (DivInvMonoid.toDiv.{u1} R (Group.toDivInvMonoid.{u1} R (CommGroup.toGroup.{u1} R _inst_1)))) x y)) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (DivInvMonoid.toDiv.{u1} R (Group.toDivInvMonoid.{u1} R (CommGroup.toGroup.{u1} R _inst_1)))) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R (DivInvMonoid.toMonoid.{u1} R (Group.toDivInvMonoid.{u1} R (CommGroup.toGroup.{u1} R _inst_1)))) _inst_2)) x) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R (DivInvMonoid.toMonoid.{u1} R (Group.toDivInvMonoid.{u1} R (CommGroup.toGroup.{u1} R _inst_1)))) _inst_2)) y))
Case conversion may be inaccurate. Consider using '#align star_div star_divₓ'. -/
/-- When multiplication is commutative, `star` preserves division. -/
@[simp]
theorem star_div [CommGroup R] [StarSemigroup R] (x y : R) : star (x / y) = star x / star y :=
  map_div (starMulAut : R ≃* R) _ _
#align star_div star_div

#print starSemigroupOfComm /-
/-- Any commutative monoid admits the trivial `*`-structure.

See note [reducible non-instances].
-/
@[reducible]
def starSemigroupOfComm {R : Type _} [CommMonoid R] : StarSemigroup R
    where
  unit := id
  star_involutive x := rfl
  star_mul := mul_comm
#align star_semigroup_of_comm starSemigroupOfComm
-/

section

attribute [local instance] starSemigroupOfComm

#print star_id_of_comm /-
/-- Note that since `star_semigroup_of_comm` is reducible, `simp` can already prove this. -/
theorem star_id_of_comm {R : Type _} [CommSemiring R] {x : R} : star x = x :=
  rfl
#align star_id_of_comm star_id_of_comm
-/

end

#print StarAddMonoid /-
/-- A `*`-additive monoid `R` is an additive monoid with an involutive `star` operation which
preserves addition.
-/
class StarAddMonoid (R : Type u) [AddMonoid R] extends InvolutiveStar R where
  star_add : ∀ r s : R, star (r + s) = star r + star s
#align star_add_monoid StarAddMonoid
-/

export StarAddMonoid (star_add)

attribute [simp] star_add

/- warning: star_add_equiv -> starAddEquiv is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddMonoid.{u1} R] [_inst_2 : StarAddMonoid.{u1} R _inst_1], AddEquiv.{u1, u1} R R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddMonoid.{u1} R] [_inst_2 : StarAddMonoid.{u1} R _inst_1], AddEquiv.{u1, u1} R R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1))
Case conversion may be inaccurate. Consider using '#align star_add_equiv starAddEquivₓ'. -/
/-- `star` as an `add_equiv` -/
@[simps apply]
def starAddEquiv [AddMonoid R] [StarAddMonoid R] : R ≃+ R :=
  {
    InvolutiveStar.star_involutive.toPerm
      star with
    toFun := star
    map_add' := star_add }
#align star_add_equiv starAddEquiv

variable (R)

/- warning: star_zero -> star_zero is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : AddMonoid.{u1} R] [_inst_2 : StarAddMonoid.{u1} R _inst_1], Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R _inst_1 _inst_2)) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)))))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : AddMonoid.{u1} R] [_inst_2 : StarAddMonoid.{u1} R _inst_1], Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R _inst_1 _inst_2)) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (AddMonoid.toZero.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (AddMonoid.toZero.{u1} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align star_zero star_zeroₓ'. -/
@[simp]
theorem star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0 :=
  (starAddEquiv : R ≃+ R).map_zero
#align star_zero star_zero

variable {R}

/- warning: star_eq_zero -> star_eq_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddMonoid.{u1} R] [_inst_2 : StarAddMonoid.{u1} R _inst_1] {x : R}, Iff (Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R _inst_1 _inst_2)) x) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)))))) (Eq.{succ u1} R x (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddMonoid.{u1} R] [_inst_2 : StarAddMonoid.{u1} R _inst_1] {x : R}, Iff (Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R _inst_1 _inst_2)) x) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (AddMonoid.toZero.{u1} R _inst_1)))) (Eq.{succ u1} R x (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (AddMonoid.toZero.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align star_eq_zero star_eq_zeroₓ'. -/
@[simp]
theorem star_eq_zero [AddMonoid R] [StarAddMonoid R] {x : R} : star x = 0 ↔ x = 0 :=
  starAddEquiv.map_eq_zero_iff
#align star_eq_zero star_eq_zero

/- warning: star_ne_zero -> star_ne_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddMonoid.{u1} R] [_inst_2 : StarAddMonoid.{u1} R _inst_1] {x : R}, Iff (Ne.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R _inst_1 _inst_2)) x) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)))))) (Ne.{succ u1} R x (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddMonoid.{u1} R] [_inst_2 : StarAddMonoid.{u1} R _inst_1] {x : R}, Iff (Ne.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R _inst_1 _inst_2)) x) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (AddMonoid.toZero.{u1} R _inst_1)))) (Ne.{succ u1} R x (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (AddMonoid.toZero.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align star_ne_zero star_ne_zeroₓ'. -/
theorem star_ne_zero [AddMonoid R] [StarAddMonoid R] {x : R} : star x ≠ 0 ↔ x ≠ 0 :=
  star_eq_zero.Not
#align star_ne_zero star_ne_zero

/- warning: star_neg -> star_neg is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddGroup.{u1} R] [_inst_2 : StarAddMonoid.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1))] (r : R), Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) _inst_2)) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) r)) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) _inst_2)) r))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddGroup.{u1} R] [_inst_2 : StarAddMonoid.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1))] (r : R), Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) _inst_2)) (Neg.neg.{u1} R (NegZeroClass.toNeg.{u1} R (SubNegZeroMonoid.toNegZeroClass.{u1} R (SubtractionMonoid.toSubNegZeroMonoid.{u1} R (AddGroup.toSubtractionMonoid.{u1} R _inst_1)))) r)) (Neg.neg.{u1} R (NegZeroClass.toNeg.{u1} R (SubNegZeroMonoid.toNegZeroClass.{u1} R (SubtractionMonoid.toSubNegZeroMonoid.{u1} R (AddGroup.toSubtractionMonoid.{u1} R _inst_1)))) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) _inst_2)) r))
Case conversion may be inaccurate. Consider using '#align star_neg star_negₓ'. -/
@[simp]
theorem star_neg [AddGroup R] [StarAddMonoid R] (r : R) : star (-r) = -star r :=
  (starAddEquiv : R ≃+ R).map_neg _
#align star_neg star_neg

/- warning: star_sub -> star_sub is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddGroup.{u1} R] [_inst_2 : StarAddMonoid.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1))] (r : R) (s : R), Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) _inst_2)) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1))) r s)) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1))) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) _inst_2)) r) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) _inst_2)) s))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddGroup.{u1} R] [_inst_2 : StarAddMonoid.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1))] (r : R) (s : R), Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) _inst_2)) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1))) r s)) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1))) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) _inst_2)) r) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R _inst_1)) _inst_2)) s))
Case conversion may be inaccurate. Consider using '#align star_sub star_subₓ'. -/
@[simp]
theorem star_sub [AddGroup R] [StarAddMonoid R] (r s : R) : star (r - s) = star r - star s :=
  (starAddEquiv : R ≃+ R).map_sub _ _
#align star_sub star_sub

#print star_nsmul /-
@[simp]
theorem star_nsmul [AddMonoid R] [StarAddMonoid R] (x : R) (n : ℕ) : star (n • x) = n • star x :=
  (starAddEquiv : R ≃+ R).toAddMonoidHom.map_nsmul _ _
#align star_nsmul star_nsmul
-/

#print star_zsmul /-
@[simp]
theorem star_zsmul [AddGroup R] [StarAddMonoid R] (x : R) (n : ℤ) : star (n • x) = n • star x :=
  (starAddEquiv : R ≃+ R).toAddMonoidHom.map_zsmul _ _
#align star_zsmul star_zsmul
-/

#print StarRing /-
/-- A `*`-ring `R` is a (semi)ring with an involutive `star` operation which is additive
which makes `R` with its multiplicative structure into a `*`-semigroup
(i.e. `star (r * s) = star s * star r`).
-/
class StarRing (R : Type u) [NonUnitalSemiring R] extends StarSemigroup R where
  star_add : ∀ r s : R, star (r + s) = star r + star s
#align star_ring StarRing
-/

#print StarRing.toStarAddMonoid /-
instance (priority := 100) StarRing.toStarAddMonoid [NonUnitalSemiring R] [StarRing R] :
    StarAddMonoid R where star_add := StarRing.star_add
#align star_ring.to_star_add_monoid StarRing.toStarAddMonoid
-/

/- warning: star_ring_equiv -> starRingEquiv is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalSemiring.{u1} R] [_inst_2 : StarRing.{u1} R _inst_1], RingEquiv.{u1, u1} R (MulOpposite.{u1} R) (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (MulOpposite.hasMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) (MulOpposite.hasAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalSemiring.{u1} R] [_inst_2 : StarRing.{u1} R _inst_1], RingEquiv.{u1, u1} R (MulOpposite.{u1} R) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)) (MulOpposite.instMulMulOpposite.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (MulOpposite.instAddMulOpposite.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align star_ring_equiv starRingEquivₓ'. -/
/-- `star` as an `ring_equiv` from `R` to `Rᵐᵒᵖ` -/
@[simps apply]
def starRingEquiv [NonUnitalSemiring R] [StarRing R] : R ≃+* Rᵐᵒᵖ :=
  { starAddEquiv.trans (MulOpposite.opAddEquiv : R ≃+ Rᵐᵒᵖ), starMulEquiv with
    toFun := fun x => MulOpposite.op (star x) }
#align star_ring_equiv starRingEquiv

#print star_natCast /-
@[simp, norm_cast]
theorem star_natCast [Semiring R] [StarRing R] (n : ℕ) : star (n : R) = n :=
  (congr_arg unop (map_natCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) n)).trans (unop_natCast _)
#align star_nat_cast star_natCast
-/

/- warning: star_int_cast -> star_intCast is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1))] (z : Int), Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1)) _inst_2))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int R (HasLiftT.mk.{1, succ u1} Int R (CoeTCₓ.coe.{1, succ u1} Int R (Int.castCoe.{u1} R (AddGroupWithOne.toHasIntCast.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) z)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int R (HasLiftT.mk.{1, succ u1} Int R (CoeTCₓ.coe.{1, succ u1} Int R (Int.castCoe.{u1} R (AddGroupWithOne.toHasIntCast.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) z)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1))] (z : Int), Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1)) _inst_2))) (Int.cast.{u1} R (Ring.toIntCast.{u1} R _inst_1) z)) (Int.cast.{u1} R (Ring.toIntCast.{u1} R _inst_1) z)
Case conversion may be inaccurate. Consider using '#align star_int_cast star_intCastₓ'. -/
@[simp, norm_cast]
theorem star_intCast [Ring R] [StarRing R] (z : ℤ) : star (z : R) = z :=
  (congr_arg unop <| map_intCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) z).trans (unop_intCast _)
#align star_int_cast star_intCast

/- warning: star_rat_cast -> star_ratCast is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : DivisionRing.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))] (r : Rat), Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) _inst_2))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat R (HasLiftT.mk.{1, succ u1} Rat R (CoeTCₓ.coe.{1, succ u1} Rat R (Rat.castCoe.{u1} R (DivisionRing.toHasRatCast.{u1} R _inst_1)))) r)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat R (HasLiftT.mk.{1, succ u1} Rat R (CoeTCₓ.coe.{1, succ u1} Rat R (Rat.castCoe.{u1} R (DivisionRing.toHasRatCast.{u1} R _inst_1)))) r)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : DivisionRing.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))] (r : Rat), Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) _inst_2))) (RatCast.ratCast.{u1} R (DivisionRing.toRatCast.{u1} R _inst_1) r)) (RatCast.ratCast.{u1} R (DivisionRing.toRatCast.{u1} R _inst_1) r)
Case conversion may be inaccurate. Consider using '#align star_rat_cast star_ratCastₓ'. -/
@[simp, norm_cast]
theorem star_ratCast [DivisionRing R] [StarRing R] (r : ℚ) : star (r : R) = r :=
  (congr_arg unop <| map_ratCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) r).trans (unop_ratCast _)
#align star_rat_cast star_ratCast

/- warning: star_ring_aut -> starRingAut is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))], RingAut.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))], RingAut.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align star_ring_aut starRingAutₓ'. -/
/-- `star` as a ring automorphism, for commutative `R`. -/
@[simps apply]
def starRingAut [CommSemiring R] [StarRing R] : RingAut R :=
  { starAddEquiv, starMulAut with toFun := star }
#align star_ring_aut starRingAut

variable (R)

#print starRingEnd /-
/-- `star` as a ring endomorphism, for commutative `R`. This is used to denote complex
conjugation, and is available under the notation `conj` in the locale `complex_conjugate`.

Note that this is the preferred form (over `star_ring_aut`, available under the same hypotheses)
because the notation `E →ₗ⋆[R] F` for an `R`-conjugate-linear map (short for
`E →ₛₗ[star_ring_end R] F`) does not pretty-print if there is a coercion involved, as would be the
case for `(↑star_ring_aut : R →* R)`. -/
def starRingEnd [CommSemiring R] [StarRing R] : R →+* R :=
  @starRingAut R _ _
#align star_ring_end starRingEnd
-/

variable {R}

-- mathport name: star_ring_end
scoped[ComplexConjugate] notation "conj" => starRingEnd hole!

/- warning: star_ring_end_apply -> starRingEnd_apply is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))] {x : R}, Eq.{succ u1} R (coeFn.{succ u1, succ u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (fun (_x : RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) => R -> R) (RingHom.hasCoeToFun.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (starRingEnd.{u1} R _inst_1 _inst_2) x) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1)) _inst_2))) x)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))] {x : R}, Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => R) x) (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => R) _x) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (RingHom.instRingHomClassRingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (starRingEnd.{u1} R _inst_1 _inst_2) x) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1)) _inst_2))) x)
Case conversion may be inaccurate. Consider using '#align star_ring_end_apply starRingEnd_applyₓ'. -/
/-- This is not a simp lemma, since we usually want simp to keep `star_ring_end` bundled.
 For example, for complex conjugation, we don't want simp to turn `conj x`
 into the bare function `star x` automatically since most lemmas are about `conj x`. -/
theorem starRingEnd_apply [CommSemiring R] [StarRing R] {x : R} : starRingEnd R x = star x :=
  rfl
#align star_ring_end_apply starRingEnd_apply

/- warning: star_ring_end_self_apply -> starRingEnd_self_apply is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))] (x : R), Eq.{succ u1} R (coeFn.{succ u1, succ u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (fun (_x : RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) => R -> R) (RingHom.hasCoeToFun.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (starRingEnd.{u1} R _inst_1 _inst_2) (coeFn.{succ u1, succ u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (fun (_x : RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) => R -> R) (RingHom.hasCoeToFun.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (starRingEnd.{u1} R _inst_1 _inst_2) x)) x
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))] (x : R), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => R) (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R (fun (a : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => R) a) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (RingHom.instRingHomClassRingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (starRingEnd.{u1} R _inst_1 _inst_2) x)) (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => R) _x) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (RingHom.instRingHomClassRingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (starRingEnd.{u1} R _inst_1 _inst_2) (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => R) _x) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (RingHom.instRingHomClassRingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (starRingEnd.{u1} R _inst_1 _inst_2) x)) x
Case conversion may be inaccurate. Consider using '#align star_ring_end_self_apply starRingEnd_self_applyₓ'. -/
@[simp]
theorem starRingEnd_self_apply [CommSemiring R] [StarRing R] (x : R) :
    starRingEnd R (starRingEnd R x) = x :=
  star_star x
#align star_ring_end_self_apply starRingEnd_self_apply

#print RingHom.involutiveStar /-
instance RingHom.involutiveStar {S : Type _} [NonAssocSemiring S] [CommSemiring R] [StarRing R] :
    InvolutiveStar (S →+* R)
    where
  toHasStar := { unit := fun f => RingHom.comp (starRingEnd R) f }
  star_involutive := by
    intro
    ext
    simp only [RingHom.coe_comp, Function.comp_apply, starRingEnd_self_apply]
#align ring_hom.has_involutive_star RingHom.involutiveStar
-/

/- warning: ring_hom.star_def -> RingHom.star_def is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : NonAssocSemiring.{u2} S] [_inst_2 : CommSemiring.{u1} R] [_inst_3 : StarRing.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_2))] (f : RingHom.{u2, u1} S R _inst_1 (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))), Eq.{succ (max u2 u1)} (RingHom.{u2, u1} S R _inst_1 (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))) (Star.star.{max u2 u1} (RingHom.{u2, u1} S R _inst_1 (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))) (InvolutiveStar.toHasStar.{max u2 u1} (RingHom.{u2, u1} S R _inst_1 (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))) (RingHom.involutiveStar.{u1, u2} R S _inst_1 _inst_2 _inst_3)) f) (RingHom.comp.{u2, u1, u1} S R R _inst_1 (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (starRingEnd.{u1} R _inst_2 _inst_3) f)
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} S] [_inst_2 : CommSemiring.{u2} R] [_inst_3 : StarRing.{u2} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u2} R (CommSemiring.toNonUnitalCommSemiring.{u2} R _inst_2))] (f : RingHom.{u1, u2} S R _inst_1 (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2))), Eq.{max (succ u2) (succ u1)} (RingHom.{u1, u2} S R _inst_1 (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2))) (Star.star.{max u2 u1} (RingHom.{u1, u2} S R _inst_1 (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2))) (InvolutiveStar.toStar.{max u2 u1} (RingHom.{u1, u2} S R _inst_1 (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2))) (RingHom.involutiveStar.{u2, u1} R S _inst_1 _inst_2 _inst_3)) f) (RingHom.comp.{u1, u2, u2} S R R _inst_1 (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2)) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2)) (starRingEnd.{u2} R _inst_2 _inst_3) f)
Case conversion may be inaccurate. Consider using '#align ring_hom.star_def RingHom.star_defₓ'. -/
theorem RingHom.star_def {S : Type _} [NonAssocSemiring S] [CommSemiring R] [StarRing R]
    (f : S →+* R) : Star.star f = RingHom.comp (starRingEnd R) f :=
  rfl
#align ring_hom.star_def RingHom.star_def

/- warning: ring_hom.star_apply -> RingHom.star_apply is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : NonAssocSemiring.{u2} S] [_inst_2 : CommSemiring.{u1} R] [_inst_3 : StarRing.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_2))] (f : RingHom.{u2, u1} S R _inst_1 (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))) (s : S), Eq.{succ u1} R (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (RingHom.{u2, u1} S R _inst_1 (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))) (fun (_x : RingHom.{u2, u1} S R _inst_1 (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))) => S -> R) (RingHom.hasCoeToFun.{u2, u1} S R _inst_1 (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))) (Star.star.{max u2 u1} (RingHom.{u2, u1} S R _inst_1 (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))) (InvolutiveStar.toHasStar.{max u2 u1} (RingHom.{u2, u1} S R _inst_1 (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))) (RingHom.involutiveStar.{u1, u2} R S _inst_1 _inst_2 _inst_3)) f) s) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_2))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_2)) _inst_3))) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (RingHom.{u2, u1} S R _inst_1 (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))) (fun (_x : RingHom.{u2, u1} S R _inst_1 (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))) => S -> R) (RingHom.hasCoeToFun.{u2, u1} S R _inst_1 (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))) f s))
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} S] [_inst_2 : CommSemiring.{u2} R] [_inst_3 : StarRing.{u2} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u2} R (CommSemiring.toNonUnitalCommSemiring.{u2} R _inst_2))] (f : RingHom.{u1, u2} S R _inst_1 (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2))) (s : S), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : S) => R) s) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (RingHom.{u1, u2} S R _inst_1 (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2))) S (fun (_x : S) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : S) => R) _x) (MulHomClass.toFunLike.{max u2 u1, u1, u2} (RingHom.{u1, u2} S R _inst_1 (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2))) S R (NonUnitalNonAssocSemiring.toMul.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S _inst_1)) (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u1, u2} (RingHom.{u1, u2} S R _inst_1 (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2))) S R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u1, u2} (RingHom.{u1, u2} S R _inst_1 (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2))) S R _inst_1 (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} S R _inst_1 (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2)))))) (Star.star.{max u2 u1} (RingHom.{u1, u2} S R _inst_1 (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2))) (InvolutiveStar.toStar.{max u2 u1} (RingHom.{u1, u2} S R _inst_1 (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2))) (RingHom.involutiveStar.{u2, u1} R S _inst_1 _inst_2 _inst_3)) f) s) (Star.star.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : S) => R) s) (InvolutiveStar.toStar.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : S) => R) s) (StarAddMonoid.toInvolutiveStar.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : S) => R) s) (AddMonoidWithOne.toAddMonoid.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : S) => R) s) (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : S) => R) s) (NonAssocSemiring.toAddCommMonoidWithOne.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : S) => R) s) (Semiring.toNonAssocSemiring.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : S) => R) s) (CommSemiring.toSemiring.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : S) => R) s) _inst_2))))) (StarRing.toStarAddMonoid.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : S) => R) s) (NonUnitalCommSemiring.toNonUnitalSemiring.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : S) => R) s) (CommSemiring.toNonUnitalCommSemiring.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : S) => R) s) _inst_2)) _inst_3))) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (RingHom.{u1, u2} S R _inst_1 (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2))) S (fun (_x : S) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : S) => R) _x) (MulHomClass.toFunLike.{max u2 u1, u1, u2} (RingHom.{u1, u2} S R _inst_1 (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2))) S R (NonUnitalNonAssocSemiring.toMul.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S _inst_1)) (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u1, u2} (RingHom.{u1, u2} S R _inst_1 (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2))) S R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u1, u2} (RingHom.{u1, u2} S R _inst_1 (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2))) S R _inst_1 (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} S R _inst_1 (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2)))))) f s))
Case conversion may be inaccurate. Consider using '#align ring_hom.star_apply RingHom.star_applyₓ'. -/
theorem RingHom.star_apply {S : Type _} [NonAssocSemiring S] [CommSemiring R] [StarRing R]
    (f : S →+* R) (s : S) : star f s = star (f s) :=
  rfl
#align ring_hom.star_apply RingHom.star_apply

/- warning: complex.conj_conj -> Complex.conj_conj is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))] (x : R), Eq.{succ u1} R (coeFn.{succ u1, succ u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (fun (_x : RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) => R -> R) (RingHom.hasCoeToFun.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (starRingEnd.{u1} R _inst_1 _inst_2) (coeFn.{succ u1, succ u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (fun (_x : RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) => R -> R) (RingHom.hasCoeToFun.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (starRingEnd.{u1} R _inst_1 _inst_2) x)) x
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))] (x : R), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => R) (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R (fun (a : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => R) a) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (RingHom.instRingHomClassRingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (starRingEnd.{u1} R _inst_1 _inst_2) x)) (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => R) _x) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (RingHom.instRingHomClassRingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (starRingEnd.{u1} R _inst_1 _inst_2) (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => R) _x) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (RingHom.instRingHomClassRingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (starRingEnd.{u1} R _inst_1 _inst_2) x)) x
Case conversion may be inaccurate. Consider using '#align complex.conj_conj Complex.conj_conjₓ'. -/
-- A more convenient name for complex conjugation
alias starRingEnd_self_apply ← Complex.conj_conj
#align complex.conj_conj Complex.conj_conj

/- warning: is_R_or_C.conj_conj -> IsROrC.conj_conj is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))] (x : R), Eq.{succ u1} R (coeFn.{succ u1, succ u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (fun (_x : RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) => R -> R) (RingHom.hasCoeToFun.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (starRingEnd.{u1} R _inst_1 _inst_2) (coeFn.{succ u1, succ u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (fun (_x : RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) => R -> R) (RingHom.hasCoeToFun.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (starRingEnd.{u1} R _inst_1 _inst_2) x)) x
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))] (x : R), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => R) (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R (fun (a : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => R) a) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (RingHom.instRingHomClassRingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (starRingEnd.{u1} R _inst_1 _inst_2) x)) (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => R) _x) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (RingHom.instRingHomClassRingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (starRingEnd.{u1} R _inst_1 _inst_2) (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => R) _x) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (RingHom.instRingHomClassRingHom.{u1, u1} R R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (starRingEnd.{u1} R _inst_1 _inst_2) x)) x
Case conversion may be inaccurate. Consider using '#align is_R_or_C.conj_conj IsROrC.conj_conjₓ'. -/
alias starRingEnd_self_apply ← IsROrC.conj_conj
#align is_R_or_C.conj_conj IsROrC.conj_conj

/- warning: star_inv' -> star_inv' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : DivisionRing.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))] (x : R), Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) _inst_2))) (Inv.inv.{u1} R (DivInvMonoid.toHasInv.{u1} R (DivisionRing.toDivInvMonoid.{u1} R _inst_1)) x)) (Inv.inv.{u1} R (DivInvMonoid.toHasInv.{u1} R (DivisionRing.toDivInvMonoid.{u1} R _inst_1)) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) _inst_2))) x))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : DivisionRing.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))] (x : R), Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) _inst_2))) (Inv.inv.{u1} R (DivisionRing.toInv.{u1} R _inst_1) x)) (Inv.inv.{u1} R (DivisionRing.toInv.{u1} R _inst_1) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R _inst_1)))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (Ring.toNonUnitalRing.{u1} R (DivisionRing.toRing.{u1} R _inst_1))) _inst_2))) x))
Case conversion may be inaccurate. Consider using '#align star_inv' star_inv'ₓ'. -/
@[simp]
theorem star_inv' [DivisionRing R] [StarRing R] (x : R) : star x⁻¹ = (star x)⁻¹ :=
  op_injective <| (map_inv₀ (starRingEquiv : R ≃+* Rᵐᵒᵖ) x).trans (op_inv (star x)).symm
#align star_inv' star_inv'

#print star_zpow₀ /-
@[simp]
theorem star_zpow₀ [DivisionRing R] [StarRing R] (x : R) (z : ℤ) : star (x ^ z) = star x ^ z :=
  op_injective <| (map_zpow₀ (starRingEquiv : R ≃+* Rᵐᵒᵖ) x z).trans (op_zpow (star x) z).symm
#align star_zpow₀ star_zpow₀
-/

/- warning: star_div' -> star_div' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Field.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (Field.toCommRing.{u1} R _inst_1))))] (x : R) (y : R), Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (Field.toCommRing.{u1} R _inst_1))))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (Field.toCommRing.{u1} R _inst_1)))) _inst_2))) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (DivInvMonoid.toHasDiv.{u1} R (DivisionRing.toDivInvMonoid.{u1} R (Field.toDivisionRing.{u1} R _inst_1)))) x y)) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (DivInvMonoid.toHasDiv.{u1} R (DivisionRing.toDivInvMonoid.{u1} R (Field.toDivisionRing.{u1} R _inst_1)))) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (Field.toCommRing.{u1} R _inst_1))))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (Field.toCommRing.{u1} R _inst_1)))) _inst_2))) x) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (Field.toCommRing.{u1} R _inst_1))))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (Field.toCommRing.{u1} R _inst_1)))) _inst_2))) y))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Field.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (Field.toCommRing.{u1} R _inst_1))))] (x : R) (y : R), Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_1))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (Field.toCommRing.{u1} R _inst_1)))) _inst_2))) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (Field.toDiv.{u1} R _inst_1)) x y)) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (Field.toDiv.{u1} R _inst_1)) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_1))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (Field.toCommRing.{u1} R _inst_1)))) _inst_2))) x) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R _inst_1))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (Field.toCommRing.{u1} R _inst_1)))) _inst_2))) y))
Case conversion may be inaccurate. Consider using '#align star_div' star_div'ₓ'. -/
/-- When multiplication is commutative, `star` preserves division. -/
@[simp]
theorem star_div' [Field R] [StarRing R] (x y : R) : star (x / y) = star x / star y :=
  map_div₀ (starRingEnd R) _ _
#align star_div' star_div'

/- warning: star_bit0 -> star_bit0 is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddMonoid.{u1} R] [_inst_2 : StarAddMonoid.{u1} R _inst_1] (r : R), Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R _inst_1 _inst_2)) (bit0.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) r)) (bit0.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R _inst_1 _inst_2)) r))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddMonoid.{u1} R] [_inst_2 : StarAddMonoid.{u1} R _inst_1] (r : R), Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R _inst_1 _inst_2)) (bit0.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) r)) (bit0.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R _inst_1 _inst_2)) r))
Case conversion may be inaccurate. Consider using '#align star_bit0 star_bit0ₓ'. -/
@[simp]
theorem star_bit0 [AddMonoid R] [StarAddMonoid R] (r : R) : star (bit0 r) = bit0 (star r) := by
  simp [bit0]
#align star_bit0 star_bit0

/- warning: star_bit1 -> star_bit1 is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] [_inst_2 : StarRing.{u1} R (Semiring.toNonUnitalSemiring.{u1} R _inst_1)] (r : R), Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonUnitalSemiring.{u1} R _inst_1)))) (StarRing.toStarAddMonoid.{u1} R (Semiring.toNonUnitalSemiring.{u1} R _inst_1) _inst_2))) (bit1.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) r)) (bit1.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonUnitalSemiring.{u1} R _inst_1)))) (StarRing.toStarAddMonoid.{u1} R (Semiring.toNonUnitalSemiring.{u1} R _inst_1) _inst_2))) r))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] [_inst_2 : StarRing.{u1} R (Semiring.toNonUnitalSemiring.{u1} R _inst_1)] (r : R), Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (StarRing.toStarAddMonoid.{u1} R (Semiring.toNonUnitalSemiring.{u1} R _inst_1) _inst_2))) (bit1.{u1} R (Semiring.toOne.{u1} R _inst_1) (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) r)) (bit1.{u1} R (Semiring.toOne.{u1} R _inst_1) (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (StarRing.toStarAddMonoid.{u1} R (Semiring.toNonUnitalSemiring.{u1} R _inst_1) _inst_2))) r))
Case conversion may be inaccurate. Consider using '#align star_bit1 star_bit1ₓ'. -/
@[simp]
theorem star_bit1 [Semiring R] [StarRing R] (r : R) : star (bit1 r) = bit1 (star r) := by
  simp [bit1]
#align star_bit1 star_bit1

#print starRingOfComm /-
/-- Any commutative semiring admits the trivial `*`-structure.

See note [reducible non-instances].
-/
@[reducible]
def starRingOfComm {R : Type _} [CommSemiring R] : StarRing R :=
  { starSemigroupOfComm with
    unit := id
    star_add := fun x y => rfl }
#align star_ring_of_comm starRingOfComm
-/

#print StarOrderedRing /-
/-- An ordered `*`-ring is a ring which is both an `ordered_add_comm_group` and a `*`-ring,
and `0 ≤ r ↔ ∃ s, r = star s * s`.
-/
class StarOrderedRing (R : Type u) [NonUnitalSemiring R] [PartialOrder R] extends StarRing R where
  add_le_add_left : ∀ a b : R, a ≤ b → ∀ c : R, c + a ≤ c + b
  nonneg_iff : ∀ r : R, 0 ≤ r ↔ ∃ s, r = star s * s
#align star_ordered_ring StarOrderedRing
-/

namespace StarOrderedRing

-- see note [lower instance priority]
instance (priority := 100) [NonUnitalRing R] [PartialOrder R] [StarOrderedRing R] :
    OrderedAddCommGroup R :=
  { show NonUnitalRing R by infer_instance, show PartialOrder R by infer_instance,
    show StarOrderedRing R by infer_instance with }

end StarOrderedRing

section NonUnitalSemiring

variable [NonUnitalSemiring R] [PartialOrder R] [StarOrderedRing R]

/- warning: star_mul_self_nonneg -> star_mul_self_nonneg is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalSemiring.{u1} R] [_inst_2 : PartialOrder.{u1} R] [_inst_3 : StarOrderedRing.{u1} R _inst_1 _inst_2] {r : R}, LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R _inst_2)) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (StarRing.toStarAddMonoid.{u1} R _inst_1 (StarOrderedRing.toStarRing.{u1} R _inst_1 _inst_2 _inst_3)))) r) r)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalSemiring.{u1} R] [_inst_2 : PartialOrder.{u1} R] [_inst_3 : StarOrderedRing.{u1} R _inst_1 _inst_2] {r : R}, LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R _inst_2)) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (SemigroupWithZero.toZero.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (StarRing.toStarAddMonoid.{u1} R _inst_1 (StarOrderedRing.toStarRing.{u1} R _inst_1 _inst_2 _inst_3)))) r) r)
Case conversion may be inaccurate. Consider using '#align star_mul_self_nonneg star_mul_self_nonnegₓ'. -/
theorem star_mul_self_nonneg {r : R} : 0 ≤ star r * r :=
  (StarOrderedRing.nonneg_iff _).mpr ⟨r, rfl⟩
#align star_mul_self_nonneg star_mul_self_nonneg

/- warning: star_mul_self_nonneg' -> star_mul_self_nonneg' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalSemiring.{u1} R] [_inst_2 : PartialOrder.{u1} R] [_inst_3 : StarOrderedRing.{u1} R _inst_1 _inst_2] {r : R}, LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R _inst_2)) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) r (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (StarRing.toStarAddMonoid.{u1} R _inst_1 (StarOrderedRing.toStarRing.{u1} R _inst_1 _inst_2 _inst_3)))) r))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalSemiring.{u1} R] [_inst_2 : PartialOrder.{u1} R] [_inst_3 : StarOrderedRing.{u1} R _inst_1 _inst_2] {r : R}, LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R _inst_2)) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (SemigroupWithZero.toZero.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) r (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (StarRing.toStarAddMonoid.{u1} R _inst_1 (StarOrderedRing.toStarRing.{u1} R _inst_1 _inst_2 _inst_3)))) r))
Case conversion may be inaccurate. Consider using '#align star_mul_self_nonneg' star_mul_self_nonneg'ₓ'. -/
theorem star_mul_self_nonneg' {r : R} : 0 ≤ r * star r :=
  by
  nth_rw_rhs 1 [← star_star r]
  exact star_mul_self_nonneg
#align star_mul_self_nonneg' star_mul_self_nonneg'

/- warning: conjugate_nonneg -> conjugate_nonneg is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalSemiring.{u1} R] [_inst_2 : PartialOrder.{u1} R] [_inst_3 : StarOrderedRing.{u1} R _inst_1 _inst_2] {a : R}, (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R _inst_2)) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))) a) -> (forall (c : R), LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R _inst_2)) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (StarRing.toStarAddMonoid.{u1} R _inst_1 (StarOrderedRing.toStarRing.{u1} R _inst_1 _inst_2 _inst_3)))) c) a) c))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalSemiring.{u1} R] [_inst_2 : PartialOrder.{u1} R] [_inst_3 : StarOrderedRing.{u1} R _inst_1 _inst_2] {a : R}, (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R _inst_2)) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (SemigroupWithZero.toZero.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R _inst_1)))) a) -> (forall (c : R), LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R _inst_2)) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (SemigroupWithZero.toZero.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (StarRing.toStarAddMonoid.{u1} R _inst_1 (StarOrderedRing.toStarRing.{u1} R _inst_1 _inst_2 _inst_3)))) c) a) c))
Case conversion may be inaccurate. Consider using '#align conjugate_nonneg conjugate_nonnegₓ'. -/
theorem conjugate_nonneg {a : R} (ha : 0 ≤ a) (c : R) : 0 ≤ star c * a * c :=
  by
  obtain ⟨x, rfl⟩ := (StarOrderedRing.nonneg_iff _).1 ha
  exact (StarOrderedRing.nonneg_iff _).2 ⟨x * c, by rw [star_mul, ← mul_assoc, mul_assoc _ _ c]⟩
#align conjugate_nonneg conjugate_nonneg

/- warning: conjugate_nonneg' -> conjugate_nonneg' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalSemiring.{u1} R] [_inst_2 : PartialOrder.{u1} R] [_inst_3 : StarOrderedRing.{u1} R _inst_1 _inst_2] {a : R}, (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R _inst_2)) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))) a) -> (forall (c : R), LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R _inst_2)) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) c a) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (StarRing.toStarAddMonoid.{u1} R _inst_1 (StarOrderedRing.toStarRing.{u1} R _inst_1 _inst_2 _inst_3)))) c)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalSemiring.{u1} R] [_inst_2 : PartialOrder.{u1} R] [_inst_3 : StarOrderedRing.{u1} R _inst_1 _inst_2] {a : R}, (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R _inst_2)) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (SemigroupWithZero.toZero.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R _inst_1)))) a) -> (forall (c : R), LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R _inst_2)) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (SemigroupWithZero.toZero.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) c a) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (StarRing.toStarAddMonoid.{u1} R _inst_1 (StarOrderedRing.toStarRing.{u1} R _inst_1 _inst_2 _inst_3)))) c)))
Case conversion may be inaccurate. Consider using '#align conjugate_nonneg' conjugate_nonneg'ₓ'. -/
theorem conjugate_nonneg' {a : R} (ha : 0 ≤ a) (c : R) : 0 ≤ c * a * star c := by
  simpa only [star_star] using conjugate_nonneg ha (star c)
#align conjugate_nonneg' conjugate_nonneg'

end NonUnitalSemiring

section NonUnitalRing

variable [NonUnitalRing R] [PartialOrder R] [StarOrderedRing R]

/- warning: conjugate_le_conjugate -> conjugate_le_conjugate is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalRing.{u1} R] [_inst_2 : PartialOrder.{u1} R] [_inst_3 : StarOrderedRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1) _inst_2] {a : R} {b : R}, (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R _inst_2)) a b) -> (forall (c : R), LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R _inst_2)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1)))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1) (StarOrderedRing.toStarRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1) _inst_2 _inst_3)))) c) a) c) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1)))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1) (StarOrderedRing.toStarRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1) _inst_2 _inst_3)))) c) b) c))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalRing.{u1} R] [_inst_2 : PartialOrder.{u1} R] [_inst_3 : StarOrderedRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1) _inst_2] {a : R} {b : R}, (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R _inst_2)) a b) -> (forall (c : R), LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R _inst_2)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1))) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (OrderedAddCommGroup.toAddCommGroup.{u1} R (StarOrderedRing.instOrderedAddCommGroup.{u1} R _inst_1 _inst_2 _inst_3))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1) (StarOrderedRing.toStarRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1) _inst_2 _inst_3)))) c) a) c) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1))) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (OrderedAddCommGroup.toAddCommGroup.{u1} R (StarOrderedRing.instOrderedAddCommGroup.{u1} R _inst_1 _inst_2 _inst_3))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1) (StarOrderedRing.toStarRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1) _inst_2 _inst_3)))) c) b) c))
Case conversion may be inaccurate. Consider using '#align conjugate_le_conjugate conjugate_le_conjugateₓ'. -/
theorem conjugate_le_conjugate {a b : R} (hab : a ≤ b) (c : R) : star c * a * c ≤ star c * b * c :=
  by
  rw [← sub_nonneg] at hab⊢
  convert conjugate_nonneg hab c
  simp only [mul_sub, sub_mul]
#align conjugate_le_conjugate conjugate_le_conjugate

/- warning: conjugate_le_conjugate' -> conjugate_le_conjugate' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalRing.{u1} R] [_inst_2 : PartialOrder.{u1} R] [_inst_3 : StarOrderedRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1) _inst_2] {a : R} {b : R}, (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R _inst_2)) a b) -> (forall (c : R), LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R _inst_2)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))) c a) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1)))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1) (StarOrderedRing.toStarRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1) _inst_2 _inst_3)))) c)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))) c b) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1)))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1) (StarOrderedRing.toStarRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1) _inst_2 _inst_3)))) c)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalRing.{u1} R] [_inst_2 : PartialOrder.{u1} R] [_inst_3 : StarOrderedRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1) _inst_2] {a : R} {b : R}, (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R _inst_2)) a b) -> (forall (c : R), LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R _inst_2)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1))) c a) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (OrderedAddCommGroup.toAddCommGroup.{u1} R (StarOrderedRing.instOrderedAddCommGroup.{u1} R _inst_1 _inst_2 _inst_3))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1) (StarOrderedRing.toStarRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1) _inst_2 _inst_3)))) c)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1))) c b) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarAddMonoid.toInvolutiveStar.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (OrderedAddCommGroup.toAddCommGroup.{u1} R (StarOrderedRing.instOrderedAddCommGroup.{u1} R _inst_1 _inst_2 _inst_3))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1) (StarOrderedRing.toStarRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1) _inst_2 _inst_3)))) c)))
Case conversion may be inaccurate. Consider using '#align conjugate_le_conjugate' conjugate_le_conjugate'ₓ'. -/
theorem conjugate_le_conjugate' {a b : R} (hab : a ≤ b) (c : R) : c * a * star c ≤ c * b * star c :=
  by simpa only [star_star] using conjugate_le_conjugate hab (star c)
#align conjugate_le_conjugate' conjugate_le_conjugate'

end NonUnitalRing

#print StarModule /-
/-- A star module `A` over a star ring `R` is a module which is a star add monoid,
and the two star structures are compatible in the sense
`star (r • a) = star r • star a`.

Note that it is up to the user of this typeclass to enforce
`[semiring R] [star_ring R] [add_comm_monoid A] [star_add_monoid A] [module R A]`, and that
the statement only requires `[has_star R] [has_star A] [has_smul R A]`.

If used as `[comm_ring R] [star_ring R] [semiring A] [star_ring A] [algebra R A]`, this represents a
star algebra.
-/
class StarModule (R : Type u) (A : Type v) [Star R] [Star A] [SMul R A] : Prop where
  star_smul : ∀ (r : R) (a : A), star (r • a) = star r • star a
#align star_module StarModule
-/

export StarModule (star_smul)

attribute [simp] star_smul

/- warning: star_semigroup.to_star_module -> StarSemigroup.to_starModule is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))], StarModule.{u1, u1} R R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) _inst_2)) (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) _inst_2)) (Mul.toSMul.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))], StarModule.{u1, u1} R R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) _inst_2)) (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) _inst_2)) (MulAction.toSMul.{u1, u1} R R (CommMonoid.toMonoid.{u1} R _inst_1) (Monoid.toMulAction.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align star_semigroup.to_star_module StarSemigroup.to_starModuleₓ'. -/
/-- A commutative star monoid is a star module over itself via `monoid.to_mul_action`. -/
instance StarSemigroup.to_starModule [CommMonoid R] [StarSemigroup R] : StarModule R R :=
  ⟨star_mul'⟩
#align star_semigroup.to_star_module StarSemigroup.to_starModule

namespace RingHomInvPair

/-- Instance needed to define star-linear maps over a commutative star ring
(ex: conjugate-linear maps when R = ℂ).  -/
instance [CommSemiring R] [StarRing R] : RingHomInvPair (starRingEnd R) (starRingEnd R) :=
  ⟨RingHom.ext star_star, RingHom.ext star_star⟩

end RingHomInvPair

section

#print StarHomClass /-
/-- `star_hom_class F R S` states that `F` is a type of `star`-preserving maps from `R` to `S`. -/
class StarHomClass (F : Type _) (R S : outParam (Type _)) [Star R] [Star S] extends
  FunLike F R fun _ => S where
  map_star : ∀ (f : F) (r : R), f (star r) = star (f r)
#align star_hom_class StarHomClass
-/

export StarHomClass (map_star)

end

/-! ### Instances -/


namespace Units

variable [Monoid R] [StarSemigroup R]

instance : StarSemigroup Rˣ
    where
  unit u :=
    { val := star u
      inv := star ↑u⁻¹
      val_inv := (star_mul _ _).symm.trans <| (congr_arg star u.inv_val).trans <| star_one _
      inv_val := (star_mul _ _).symm.trans <| (congr_arg star u.val_inv).trans <| star_one _ }
  star_involutive u := Units.ext (star_involutive _)
  star_mul u v := Units.ext (star_mul _ _)

/- warning: units.coe_star -> Units.coe_star is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Monoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R _inst_1)] (u : Units.{u1} R _inst_1), Eq.{succ u1} R ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R _inst_1) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R _inst_1) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R _inst_1) R (coeBase.{succ u1, succ u1} (Units.{u1} R _inst_1) R (Units.hasCoe.{u1} R _inst_1)))) (Star.star.{u1} (Units.{u1} R _inst_1) (InvolutiveStar.toHasStar.{u1} (Units.{u1} R _inst_1) (StarSemigroup.toHasInvolutiveStar.{u1} (Units.{u1} R _inst_1) (Monoid.toSemigroup.{u1} (Units.{u1} R _inst_1) (DivInvMonoid.toMonoid.{u1} (Units.{u1} R _inst_1) (Group.toDivInvMonoid.{u1} (Units.{u1} R _inst_1) (Units.group.{u1} R _inst_1)))) (Units.starSemigroup.{u1} R _inst_1 _inst_2))) u)) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R _inst_1) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R _inst_1) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R _inst_1) R (coeBase.{succ u1, succ u1} (Units.{u1} R _inst_1) R (Units.hasCoe.{u1} R _inst_1)))) u))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Monoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R _inst_1)] (u : Units.{u1} R _inst_1), Eq.{succ u1} R (Units.val.{u1} R _inst_1 (Star.star.{u1} (Units.{u1} R _inst_1) (InvolutiveStar.toStar.{u1} (Units.{u1} R _inst_1) (StarSemigroup.toInvolutiveStar.{u1} (Units.{u1} R _inst_1) (Monoid.toSemigroup.{u1} (Units.{u1} R _inst_1) (DivInvMonoid.toMonoid.{u1} (Units.{u1} R _inst_1) (Group.toDivInvMonoid.{u1} (Units.{u1} R _inst_1) (Units.instGroupUnits.{u1} R _inst_1)))) (Units.instStarSemigroupUnitsToSemigroupToMonoidToDivInvMonoidInstGroupUnits.{u1} R _inst_1 _inst_2))) u)) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) (Units.val.{u1} R _inst_1 u))
Case conversion may be inaccurate. Consider using '#align units.coe_star Units.coe_starₓ'. -/
@[simp]
theorem coe_star (u : Rˣ) : ↑(star u) = (star ↑u : R) :=
  rfl
#align units.coe_star Units.coe_star

/- warning: units.coe_star_inv -> Units.coe_star_inv is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Monoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R _inst_1)] (u : Units.{u1} R _inst_1), Eq.{succ u1} R ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R _inst_1) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R _inst_1) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R _inst_1) R (coeBase.{succ u1, succ u1} (Units.{u1} R _inst_1) R (Units.hasCoe.{u1} R _inst_1)))) (Inv.inv.{u1} (Units.{u1} R _inst_1) (Units.hasInv.{u1} R _inst_1) (Star.star.{u1} (Units.{u1} R _inst_1) (InvolutiveStar.toHasStar.{u1} (Units.{u1} R _inst_1) (StarSemigroup.toHasInvolutiveStar.{u1} (Units.{u1} R _inst_1) (Monoid.toSemigroup.{u1} (Units.{u1} R _inst_1) (DivInvMonoid.toMonoid.{u1} (Units.{u1} R _inst_1) (Group.toDivInvMonoid.{u1} (Units.{u1} R _inst_1) (Units.group.{u1} R _inst_1)))) (Units.starSemigroup.{u1} R _inst_1 _inst_2))) u))) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R _inst_1) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R _inst_1) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R _inst_1) R (coeBase.{succ u1, succ u1} (Units.{u1} R _inst_1) R (Units.hasCoe.{u1} R _inst_1)))) (Inv.inv.{u1} (Units.{u1} R _inst_1) (Units.hasInv.{u1} R _inst_1) u)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Monoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R _inst_1)] (u : Units.{u1} R _inst_1), Eq.{succ u1} R (Units.val.{u1} R _inst_1 (Inv.inv.{u1} (Units.{u1} R _inst_1) (Units.instInvUnits.{u1} R _inst_1) (Star.star.{u1} (Units.{u1} R _inst_1) (InvolutiveStar.toStar.{u1} (Units.{u1} R _inst_1) (StarSemigroup.toInvolutiveStar.{u1} (Units.{u1} R _inst_1) (Monoid.toSemigroup.{u1} (Units.{u1} R _inst_1) (DivInvMonoid.toMonoid.{u1} (Units.{u1} R _inst_1) (Group.toDivInvMonoid.{u1} (Units.{u1} R _inst_1) (Units.instGroupUnits.{u1} R _inst_1)))) (Units.instStarSemigroupUnitsToSemigroupToMonoidToDivInvMonoidInstGroupUnits.{u1} R _inst_1 _inst_2))) u))) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) (Units.val.{u1} R _inst_1 (Inv.inv.{u1} (Units.{u1} R _inst_1) (Units.instInvUnits.{u1} R _inst_1) u)))
Case conversion may be inaccurate. Consider using '#align units.coe_star_inv Units.coe_star_invₓ'. -/
@[simp]
theorem coe_star_inv (u : Rˣ) : ↑(star u)⁻¹ = (star ↑u⁻¹ : R) :=
  rfl
#align units.coe_star_inv Units.coe_star_inv

instance {A : Type _} [Star A] [SMul R A] [StarModule R A] : StarModule Rˣ A :=
  ⟨fun u a => (star_smul (↑u) a : _)⟩

end Units

#print IsUnit.star /-
theorem IsUnit.star [Monoid R] [StarSemigroup R] {a : R} : IsUnit a → IsUnit (star a)
  | ⟨u, hu⟩ => ⟨star u, hu ▸ rfl⟩
#align is_unit.star IsUnit.star
-/

#print isUnit_star /-
@[simp]
theorem isUnit_star [Monoid R] [StarSemigroup R] {a : R} : IsUnit (star a) ↔ IsUnit a :=
  ⟨fun h => star_star a ▸ h.unit, IsUnit.star⟩
#align is_unit_star isUnit_star
-/

#print Ring.inverse_star /-
theorem Ring.inverse_star [Semiring R] [StarRing R] (a : R) :
    Ring.inverse (star a) = star (Ring.inverse a) :=
  by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [Ring.inverse_unit, ← Units.coe_star, Ring.inverse_unit, ← Units.coe_star_inv]
  rw [Ring.inverse_non_unit _ ha, Ring.inverse_non_unit _ (mt is_unit_star.mp ha), star_zero]
#align ring.inverse_star Ring.inverse_star
-/

/- warning: invertible.star -> Invertible.star is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Monoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R _inst_1)] (r : R) [_inst_3 : Invertible.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (MulOneClass.toHasOne.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) r], Invertible.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (MulOneClass.toHasOne.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) r)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Monoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R _inst_1)] (r : R) [_inst_3 : Invertible.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (Monoid.toOne.{u1} R _inst_1) r], Invertible.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (Monoid.toOne.{u1} R _inst_1) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) r)
Case conversion may be inaccurate. Consider using '#align invertible.star Invertible.starₓ'. -/
instance Invertible.star {R : Type _} [Monoid R] [StarSemigroup R] (r : R) [Invertible r] :
    Invertible (star r) where
  invOf := star (⅟ r)
  invOf_mul_self := by rw [← star_mul, mul_invOf_self, star_one]
  mul_invOf_self := by rw [← star_mul, invOf_mul_self, star_one]
#align invertible.star Invertible.star

/- warning: star_inv_of -> star_invOf is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Monoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R _inst_1)] (r : R) [_inst_3 : Invertible.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (MulOneClass.toHasOne.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) r] [_inst_4 : Invertible.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (MulOneClass.toHasOne.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) r)], Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) (Invertible.invOf.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (MulOneClass.toHasOne.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) r _inst_3)) (Invertible.invOf.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (MulOneClass.toHasOne.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (Star.star.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) r) _inst_4)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Monoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R _inst_1)] (r : R) [_inst_3 : Invertible.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (Monoid.toOne.{u1} R _inst_1) r] [_inst_4 : Invertible.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (Monoid.toOne.{u1} R _inst_1) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) r)], Eq.{succ u1} R (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) (Invertible.invOf.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (Monoid.toOne.{u1} R _inst_1) r _inst_3)) (Invertible.invOf.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (Monoid.toOne.{u1} R _inst_1) (Star.star.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R _inst_1) _inst_2)) r) _inst_4)
Case conversion may be inaccurate. Consider using '#align star_inv_of star_invOfₓ'. -/
theorem star_invOf {R : Type _} [Monoid R] [StarSemigroup R] (r : R) [Invertible r]
    [Invertible (star r)] : star (⅟ r) = ⅟ (star r) :=
  by
  letI := Invertible.star r
  convert (rfl : star (⅟ r) = _)
#align star_inv_of star_invOf

namespace MulOpposite

/-- The opposite type carries the same star operation. -/
instance [Star R] : Star Rᵐᵒᵖ where unit r := op (star r.unop)

#print MulOpposite.unop_star /-
@[simp]
theorem unop_star [Star R] (r : Rᵐᵒᵖ) : unop (star r) = star (unop r) :=
  rfl
#align mul_opposite.unop_star MulOpposite.unop_star
-/

#print MulOpposite.op_star /-
@[simp]
theorem op_star [Star R] (r : R) : op (star r) = star (op r) :=
  rfl
#align mul_opposite.op_star MulOpposite.op_star
-/

instance [InvolutiveStar R] : InvolutiveStar Rᵐᵒᵖ
    where star_involutive r := unop_injective (star_star r.unop)

instance [Monoid R] [StarSemigroup R] : StarSemigroup Rᵐᵒᵖ
    where star_mul x y := unop_injective (star_mul y.unop x.unop)

instance [AddMonoid R] [StarAddMonoid R] : StarAddMonoid Rᵐᵒᵖ
    where star_add x y := unop_injective (star_add x.unop y.unop)

instance [Semiring R] [StarRing R] : StarRing Rᵐᵒᵖ :=
  { MulOpposite.starAddMonoid with }

end MulOpposite

/- warning: star_semigroup.to_opposite_star_module -> StarSemigroup.toOpposite_starModule is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))], StarModule.{u1, u1} (MulOpposite.{u1} R) R (MulOpposite.hasStar.{u1} R (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) _inst_2))) (InvolutiveStar.toHasStar.{u1} R (StarSemigroup.toHasInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) _inst_2)) (Mul.toHasOppositeSMul.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] [_inst_2 : StarSemigroup.{u1} R (Monoid.toSemigroup.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))], StarModule.{u1, u1} (MulOpposite.{u1} R) R (MulOpposite.instStarMulOpposite.{u1} R (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) _inst_2))) (InvolutiveStar.toStar.{u1} R (StarSemigroup.toInvolutiveStar.{u1} R (Monoid.toSemigroup.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) _inst_2)) (Mul.toHasOppositeSMul.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align star_semigroup.to_opposite_star_module StarSemigroup.toOpposite_starModuleₓ'. -/
/-- A commutative star monoid is a star module over its opposite via
`monoid.to_opposite_mul_action`. -/
instance StarSemigroup.toOpposite_starModule [CommMonoid R] [StarSemigroup R] : StarModule Rᵐᵒᵖ R :=
  ⟨fun r s => star_mul' s r.unop⟩
#align star_semigroup.to_opposite_star_module StarSemigroup.toOpposite_starModule

