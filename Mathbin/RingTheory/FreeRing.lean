/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Johan Commelin

! This file was ported from Lean 3 source module ring_theory.free_ring
! leanprover-community/mathlib commit 932872382355f00112641d305ba0619305dc8642
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.FreeAbelianGroup

/-!
# Free rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The theory of the free ring over a type.

## Main definitions

* `free_ring α` : the free (not commutative in general) ring over a type.
* `lift (f : α → R)` : the ring hom `free_ring α →+* R` induced by `f`.
* `map (f : α → β)` : the ring hom `free_ring α →+* free_ring β` induced by `f`.

## Implementation details

`free_ring α` is implemented as the free abelian group over the free monoid on `α`.

## Tags

free ring

-/


universe u v

#print FreeRing /-
/-- The free ring over a type `α`. -/
def FreeRing (α : Type u) : Type u :=
  FreeAbelianGroup <| FreeMonoid α deriving Ring, Inhabited
#align free_ring FreeRing
-/

namespace FreeRing

variable {α : Type u}

#print FreeRing.of /-
/-- The canonical map from α to `free_ring α`. -/
def of (x : α) : FreeRing α :=
  FreeAbelianGroup.of (FreeMonoid.of x)
#align free_ring.of FreeRing.of
-/

#print FreeRing.of_injective /-
theorem of_injective : Function.Injective (of : α → FreeRing α) :=
  FreeAbelianGroup.of_injective.comp FreeMonoid.of_injective
#align free_ring.of_injective FreeRing.of_injective
-/

/- warning: free_ring.induction_on -> FreeRing.induction_on is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {C : (FreeRing.{u1} α) -> Prop} (z : FreeRing.{u1} α), (C (Neg.neg.{u1} (FreeRing.{u1} α) (SubNegMonoid.toHasNeg.{u1} (FreeRing.{u1} α) (AddGroup.toSubNegMonoid.{u1} (FreeRing.{u1} α) (AddGroupWithOne.toAddGroup.{u1} (FreeRing.{u1} α) (AddCommGroupWithOne.toAddGroupWithOne.{u1} (FreeRing.{u1} α) (Ring.toAddCommGroupWithOne.{u1} (FreeRing.{u1} α) (FreeRing.ring.{u1} α)))))) (OfNat.ofNat.{u1} (FreeRing.{u1} α) 1 (OfNat.mk.{u1} (FreeRing.{u1} α) 1 (One.one.{u1} (FreeRing.{u1} α) (AddMonoidWithOne.toOne.{u1} (FreeRing.{u1} α) (AddGroupWithOne.toAddMonoidWithOne.{u1} (FreeRing.{u1} α) (AddCommGroupWithOne.toAddGroupWithOne.{u1} (FreeRing.{u1} α) (Ring.toAddCommGroupWithOne.{u1} (FreeRing.{u1} α) (FreeRing.ring.{u1} α)))))))))) -> (forall (b : α), C (FreeRing.of.{u1} α b)) -> (forall (x : FreeRing.{u1} α) (y : FreeRing.{u1} α), (C x) -> (C y) -> (C (HAdd.hAdd.{u1, u1, u1} (FreeRing.{u1} α) (FreeRing.{u1} α) (FreeRing.{u1} α) (instHAdd.{u1} (FreeRing.{u1} α) (Distrib.toHasAdd.{u1} (FreeRing.{u1} α) (Ring.toDistrib.{u1} (FreeRing.{u1} α) (FreeRing.ring.{u1} α)))) x y))) -> (forall (x : FreeRing.{u1} α) (y : FreeRing.{u1} α), (C x) -> (C y) -> (C (HMul.hMul.{u1, u1, u1} (FreeRing.{u1} α) (FreeRing.{u1} α) (FreeRing.{u1} α) (instHMul.{u1} (FreeRing.{u1} α) (Distrib.toHasMul.{u1} (FreeRing.{u1} α) (Ring.toDistrib.{u1} (FreeRing.{u1} α) (FreeRing.ring.{u1} α)))) x y))) -> (C z)
but is expected to have type
  forall {α : Type.{u1}} {C : (FreeRing.{u1} α) -> Prop} (z : FreeRing.{u1} α), (C (Neg.neg.{u1} (FreeRing.{u1} α) (Ring.toNeg.{u1} (FreeRing.{u1} α) (instRingFreeRing.{u1} α)) (OfNat.ofNat.{u1} (FreeRing.{u1} α) 1 (One.toOfNat1.{u1} (FreeRing.{u1} α) (Semiring.toOne.{u1} (FreeRing.{u1} α) (Ring.toSemiring.{u1} (FreeRing.{u1} α) (instRingFreeRing.{u1} α))))))) -> (forall (b : α), C (FreeRing.of.{u1} α b)) -> (forall (x : FreeRing.{u1} α) (y : FreeRing.{u1} α), (C x) -> (C y) -> (C (HAdd.hAdd.{u1, u1, u1} (FreeRing.{u1} α) (FreeRing.{u1} α) (FreeRing.{u1} α) (instHAdd.{u1} (FreeRing.{u1} α) (Distrib.toAdd.{u1} (FreeRing.{u1} α) (NonUnitalNonAssocSemiring.toDistrib.{u1} (FreeRing.{u1} α) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} (FreeRing.{u1} α) (NonAssocRing.toNonUnitalNonAssocRing.{u1} (FreeRing.{u1} α) (Ring.toNonAssocRing.{u1} (FreeRing.{u1} α) (instRingFreeRing.{u1} α))))))) x y))) -> (forall (x : FreeRing.{u1} α) (y : FreeRing.{u1} α), (C x) -> (C y) -> (C (HMul.hMul.{u1, u1, u1} (FreeRing.{u1} α) (FreeRing.{u1} α) (FreeRing.{u1} α) (instHMul.{u1} (FreeRing.{u1} α) (NonUnitalNonAssocRing.toMul.{u1} (FreeRing.{u1} α) (NonAssocRing.toNonUnitalNonAssocRing.{u1} (FreeRing.{u1} α) (Ring.toNonAssocRing.{u1} (FreeRing.{u1} α) (instRingFreeRing.{u1} α))))) x y))) -> (C z)
Case conversion may be inaccurate. Consider using '#align free_ring.induction_on FreeRing.induction_onₓ'. -/
@[elab_as_elim]
protected theorem induction_on {C : FreeRing α → Prop} (z : FreeRing α) (hn1 : C (-1))
    (hb : ∀ b, C (of b)) (ha : ∀ x y, C x → C y → C (x + y)) (hm : ∀ x y, C x → C y → C (x * y)) :
    C z :=
  have hn : ∀ x, C x → C (-x) := fun x ih => neg_one_mul x ▸ hm _ _ hn1 ih
  have h1 : C 1 := neg_neg (1 : FreeRing α) ▸ hn _ hn1
  FreeAbelianGroup.induction_on z (add_left_neg (1 : FreeRing α) ▸ ha _ _ hn1 h1)
    (fun m => List.recOn m h1 fun a m ih => hm _ _ (hb a) ih) (fun m ih => hn _ ih) ha
#align free_ring.induction_on FreeRing.induction_on

section lift

variable {R : Type v} [Ring R] (f : α → R)

#print FreeRing.lift /-
/-- The ring homomorphism `free_ring α →+* R` induced from a map `α → R`. -/
def lift : (α → R) ≃ (FreeRing α →+* R) :=
  FreeMonoid.lift.trans FreeAbelianGroup.liftMonoid
#align free_ring.lift FreeRing.lift
-/

/- warning: free_ring.lift_of -> FreeRing.lift_of is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : Ring.{u2} R] (f : α -> R) (x : α), Eq.{succ u2} R (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} (FreeRing.{u1} α) R (NonAssocRing.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toNonAssocRing.{u1} (FreeRing.{u1} α) (FreeRing.ring.{u1} α))) (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1))) (fun (_x : RingHom.{u1, u2} (FreeRing.{u1} α) R (NonAssocRing.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toNonAssocRing.{u1} (FreeRing.{u1} α) (FreeRing.ring.{u1} α))) (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1))) => (FreeRing.{u1} α) -> R) (RingHom.hasCoeToFun.{u1, u2} (FreeRing.{u1} α) R (NonAssocRing.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toNonAssocRing.{u1} (FreeRing.{u1} α) (FreeRing.ring.{u1} α))) (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1))) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (α -> R) (RingHom.{u1, u2} (FreeRing.{u1} α) R (NonAssocRing.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toNonAssocRing.{u1} (FreeRing.{u1} α) (FreeRing.ring.{u1} α))) (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)))) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (α -> R) (RingHom.{u1, u2} (FreeRing.{u1} α) R (NonAssocRing.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toNonAssocRing.{u1} (FreeRing.{u1} α) (FreeRing.ring.{u1} α))) (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)))) => (α -> R) -> (RingHom.{u1, u2} (FreeRing.{u1} α) R (NonAssocRing.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toNonAssocRing.{u1} (FreeRing.{u1} α) (FreeRing.ring.{u1} α))) (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)))) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (α -> R) (RingHom.{u1, u2} (FreeRing.{u1} α) R (NonAssocRing.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toNonAssocRing.{u1} (FreeRing.{u1} α) (FreeRing.ring.{u1} α))) (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)))) (FreeRing.lift.{u1, u2} α R _inst_1) f) (FreeRing.of.{u1} α x)) (f x)
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : Ring.{u2} R] (f : α -> R) (x : α), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : FreeRing.{u1} α) => R) (FreeRing.of.{u1} α x)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : α -> R) => RingHom.{u1, u2} (FreeRing.{u1} α) R (Semiring.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toSemiring.{u1} (FreeRing.{u1} α) (instRingFreeRing.{u1} α))) (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) f) (FreeRing.{u1} α) (fun (_x : FreeRing.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : FreeRing.{u1} α) => R) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : α -> R) => RingHom.{u1, u2} (FreeRing.{u1} α) R (Semiring.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toSemiring.{u1} (FreeRing.{u1} α) (instRingFreeRing.{u1} α))) (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) f) (FreeRing.{u1} α) R (NonUnitalNonAssocSemiring.toMul.{u1} (FreeRing.{u1} α) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (FreeRing.{u1} α) (Semiring.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toSemiring.{u1} (FreeRing.{u1} α) (instRingFreeRing.{u1} α))))) (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : α -> R) => RingHom.{u1, u2} (FreeRing.{u1} α) R (Semiring.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toSemiring.{u1} (FreeRing.{u1} α) (instRingFreeRing.{u1} α))) (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) f) (FreeRing.{u1} α) R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (FreeRing.{u1} α) (Semiring.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toSemiring.{u1} (FreeRing.{u1} α) (instRingFreeRing.{u1} α)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : α -> R) => RingHom.{u1, u2} (FreeRing.{u1} α) R (Semiring.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toSemiring.{u1} (FreeRing.{u1} α) (instRingFreeRing.{u1} α))) (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) f) (FreeRing.{u1} α) R (Semiring.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toSemiring.{u1} (FreeRing.{u1} α) (instRingFreeRing.{u1} α))) (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)) (RingHom.instRingHomClassRingHom.{u1, u2} (FreeRing.{u1} α) R (Semiring.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toSemiring.{u1} (FreeRing.{u1} α) (instRingFreeRing.{u1} α))) (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))))) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (α -> R) (RingHom.{u1, u2} (FreeRing.{u1} α) R (Semiring.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toSemiring.{u1} (FreeRing.{u1} α) (instRingFreeRing.{u1} α))) (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) (α -> R) (fun (_x : α -> R) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : α -> R) => RingHom.{u1, u2} (FreeRing.{u1} α) R (Semiring.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toSemiring.{u1} (FreeRing.{u1} α) (instRingFreeRing.{u1} α))) (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (α -> R) (RingHom.{u1, u2} (FreeRing.{u1} α) R (Semiring.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toSemiring.{u1} (FreeRing.{u1} α) (instRingFreeRing.{u1} α))) (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) (FreeRing.lift.{u1, u2} α R _inst_1) f) (FreeRing.of.{u1} α x)) (f x)
Case conversion may be inaccurate. Consider using '#align free_ring.lift_of FreeRing.lift_ofₓ'. -/
@[simp]
theorem lift_of (x : α) : lift f (of x) = f x :=
  congr_fun (lift.left_inv f) x
#align free_ring.lift_of FreeRing.lift_of

#print FreeRing.lift_comp_of /-
@[simp]
theorem lift_comp_of (f : FreeRing α →+* R) : lift (f ∘ of) = f :=
  lift.right_inv f
#align free_ring.lift_comp_of FreeRing.lift_comp_of
-/

#print FreeRing.hom_ext /-
@[ext]
theorem hom_ext ⦃f g : FreeRing α →+* R⦄ (h : ∀ x, f (of x) = g (of x)) : f = g :=
  lift.symm.Injective (funext h)
#align free_ring.hom_ext FreeRing.hom_ext
-/

end lift

variable {β : Type v} (f : α → β)

#print FreeRing.map /-
/-- The canonical ring homomorphism `free_ring α →+* free_ring β` generated by a map `α → β`. -/
def map : FreeRing α →+* FreeRing β :=
  lift <| of ∘ f
#align free_ring.map FreeRing.map
-/

/- warning: free_ring.map_of -> FreeRing.map_of is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (x : α), Eq.{succ u2} (FreeRing.{u2} β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} (FreeRing.{u1} α) (FreeRing.{u2} β) (NonAssocRing.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toNonAssocRing.{u1} (FreeRing.{u1} α) (FreeRing.ring.{u1} α))) (NonAssocRing.toNonAssocSemiring.{u2} (FreeRing.{u2} β) (Ring.toNonAssocRing.{u2} (FreeRing.{u2} β) (FreeRing.ring.{u2} β)))) (fun (_x : RingHom.{u1, u2} (FreeRing.{u1} α) (FreeRing.{u2} β) (NonAssocRing.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toNonAssocRing.{u1} (FreeRing.{u1} α) (FreeRing.ring.{u1} α))) (NonAssocRing.toNonAssocSemiring.{u2} (FreeRing.{u2} β) (Ring.toNonAssocRing.{u2} (FreeRing.{u2} β) (FreeRing.ring.{u2} β)))) => (FreeRing.{u1} α) -> (FreeRing.{u2} β)) (RingHom.hasCoeToFun.{u1, u2} (FreeRing.{u1} α) (FreeRing.{u2} β) (NonAssocRing.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toNonAssocRing.{u1} (FreeRing.{u1} α) (FreeRing.ring.{u1} α))) (NonAssocRing.toNonAssocSemiring.{u2} (FreeRing.{u2} β) (Ring.toNonAssocRing.{u2} (FreeRing.{u2} β) (FreeRing.ring.{u2} β)))) (FreeRing.map.{u1, u2} α β f) (FreeRing.of.{u1} α x)) (FreeRing.of.{u2} β (f x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (x : α), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : FreeRing.{u1} α) => FreeRing.{u2} β) (FreeRing.of.{u1} α x)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} (FreeRing.{u1} α) (FreeRing.{u2} β) (Semiring.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toSemiring.{u1} (FreeRing.{u1} α) (instRingFreeRing.{u1} α))) (Semiring.toNonAssocSemiring.{u2} (FreeRing.{u2} β) (Ring.toSemiring.{u2} (FreeRing.{u2} β) (instRingFreeRing.{u2} β)))) (FreeRing.{u1} α) (fun (_x : FreeRing.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : FreeRing.{u1} α) => FreeRing.{u2} β) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} (FreeRing.{u1} α) (FreeRing.{u2} β) (Semiring.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toSemiring.{u1} (FreeRing.{u1} α) (instRingFreeRing.{u1} α))) (Semiring.toNonAssocSemiring.{u2} (FreeRing.{u2} β) (Ring.toSemiring.{u2} (FreeRing.{u2} β) (instRingFreeRing.{u2} β)))) (FreeRing.{u1} α) (FreeRing.{u2} β) (NonUnitalNonAssocSemiring.toMul.{u1} (FreeRing.{u1} α) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (FreeRing.{u1} α) (Semiring.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toSemiring.{u1} (FreeRing.{u1} α) (instRingFreeRing.{u1} α))))) (NonUnitalNonAssocSemiring.toMul.{u2} (FreeRing.{u2} β) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} (FreeRing.{u2} β) (Semiring.toNonAssocSemiring.{u2} (FreeRing.{u2} β) (Ring.toSemiring.{u2} (FreeRing.{u2} β) (instRingFreeRing.{u2} β))))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} (FreeRing.{u1} α) (FreeRing.{u2} β) (Semiring.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toSemiring.{u1} (FreeRing.{u1} α) (instRingFreeRing.{u1} α))) (Semiring.toNonAssocSemiring.{u2} (FreeRing.{u2} β) (Ring.toSemiring.{u2} (FreeRing.{u2} β) (instRingFreeRing.{u2} β)))) (FreeRing.{u1} α) (FreeRing.{u2} β) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (FreeRing.{u1} α) (Semiring.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toSemiring.{u1} (FreeRing.{u1} α) (instRingFreeRing.{u1} α)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} (FreeRing.{u2} β) (Semiring.toNonAssocSemiring.{u2} (FreeRing.{u2} β) (Ring.toSemiring.{u2} (FreeRing.{u2} β) (instRingFreeRing.{u2} β)))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} (FreeRing.{u1} α) (FreeRing.{u2} β) (Semiring.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toSemiring.{u1} (FreeRing.{u1} α) (instRingFreeRing.{u1} α))) (Semiring.toNonAssocSemiring.{u2} (FreeRing.{u2} β) (Ring.toSemiring.{u2} (FreeRing.{u2} β) (instRingFreeRing.{u2} β)))) (FreeRing.{u1} α) (FreeRing.{u2} β) (Semiring.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toSemiring.{u1} (FreeRing.{u1} α) (instRingFreeRing.{u1} α))) (Semiring.toNonAssocSemiring.{u2} (FreeRing.{u2} β) (Ring.toSemiring.{u2} (FreeRing.{u2} β) (instRingFreeRing.{u2} β))) (RingHom.instRingHomClassRingHom.{u1, u2} (FreeRing.{u1} α) (FreeRing.{u2} β) (Semiring.toNonAssocSemiring.{u1} (FreeRing.{u1} α) (Ring.toSemiring.{u1} (FreeRing.{u1} α) (instRingFreeRing.{u1} α))) (Semiring.toNonAssocSemiring.{u2} (FreeRing.{u2} β) (Ring.toSemiring.{u2} (FreeRing.{u2} β) (instRingFreeRing.{u2} β))))))) (FreeRing.map.{u1, u2} α β f) (FreeRing.of.{u1} α x)) (FreeRing.of.{u2} β (f x))
Case conversion may be inaccurate. Consider using '#align free_ring.map_of FreeRing.map_ofₓ'. -/
@[simp]
theorem map_of (x : α) : map f (of x) = of (f x) :=
  lift_of _ _
#align free_ring.map_of FreeRing.map_of

end FreeRing

