/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland

! This file was ported from Lean 3 source module algebra.ring.basic
! leanprover-community/mathlib commit d3e8e0a0237c10c2627bf52c246b15ff8e7df4c0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Ring.Defs
import Mathbin.Algebra.Hom.Group
import Mathbin.Algebra.Opposites

/-!
# Semirings and rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file gives lemmas about semirings, rings and domains.
This is analogous to `algebra.group.basic`,
the difference being that the former is about `+` and `*` separately, while
the present file is about their interaction.

For the definitions of semirings and rings see `algebra.ring.defs`.

-/


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open Function

namespace AddHom

/- warning: add_hom.mul_left -> AddHom.mulLeft is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Distrib.{u1} R], R -> (AddHom.{u1, u1} R R (Distrib.toHasAdd.{u1} R _inst_1) (Distrib.toHasAdd.{u1} R _inst_1))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Distrib.{u1} R], R -> (AddHom.{u1, u1} R R (Distrib.toAdd.{u1} R _inst_1) (Distrib.toAdd.{u1} R _inst_1))
Case conversion may be inaccurate. Consider using '#align add_hom.mul_left AddHom.mulLeftₓ'. -/
/-- Left multiplication by an element of a type with distributive multiplication is an `add_hom`. -/
@[simps (config := { fullyApplied := false })]
def mulLeft {R : Type _} [Distrib R] (r : R) : AddHom R R :=
  ⟨(· * ·) r, mul_add r⟩
#align add_hom.mul_left AddHom.mulLeft

/- warning: add_hom.mul_right -> AddHom.mulRight is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Distrib.{u1} R], R -> (AddHom.{u1, u1} R R (Distrib.toHasAdd.{u1} R _inst_1) (Distrib.toHasAdd.{u1} R _inst_1))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Distrib.{u1} R], R -> (AddHom.{u1, u1} R R (Distrib.toAdd.{u1} R _inst_1) (Distrib.toAdd.{u1} R _inst_1))
Case conversion may be inaccurate. Consider using '#align add_hom.mul_right AddHom.mulRightₓ'. -/
/-- Left multiplication by an element of a type with distributive multiplication is an `add_hom`. -/
@[simps (config := { fullyApplied := false })]
def mulRight {R : Type _} [Distrib R] (r : R) : AddHom R R :=
  ⟨fun a => a * r, fun _ _ => add_mul _ _ r⟩
#align add_hom.mul_right AddHom.mulRight

end AddHom

section AddHomClass

variable {F : Type _} [NonAssocSemiring α] [NonAssocSemiring β] [AddHomClass F α β]

/- warning: map_bit0 -> map_bit0 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {F : Type.{u3}} [_inst_1 : NonAssocSemiring.{u1} α] [_inst_2 : NonAssocSemiring.{u2} β] [_inst_3 : AddHomClass.{u3, u1, u2} F α β (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (Distrib.toHasAdd.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_2)))] (f : F) (a : α), Eq.{succ u2} β (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F α (fun (_x : α) => β) (AddHomClass.toFunLike.{u3, u1, u2} F α β (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (Distrib.toHasAdd.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_2))) _inst_3)) f (bit0.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) a)) (bit0.{u2} β (Distrib.toHasAdd.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_2))) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F α (fun (_x : α) => β) (AddHomClass.toFunLike.{u3, u1, u2} F α β (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (Distrib.toHasAdd.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_2))) _inst_3)) f a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {F : Type.{u1}} [_inst_1 : NonAssocSemiring.{u2} α] [_inst_2 : NonAssocSemiring.{u3} β] [_inst_3 : AddHomClass.{u1, u2, u3} F α β (Distrib.toAdd.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_1))) (Distrib.toAdd.{u3} β (NonUnitalNonAssocSemiring.toDistrib.{u3} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} β _inst_2)))] (f : F) (a : α), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => β) (bit0.{u2} α (Distrib.toAdd.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_1))) a)) (FunLike.coe.{succ u1, succ u2, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => β) _x) (AddHomClass.toFunLike.{u1, u2, u3} F α β (Distrib.toAdd.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_1))) (Distrib.toAdd.{u3} β (NonUnitalNonAssocSemiring.toDistrib.{u3} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} β _inst_2))) _inst_3) f (bit0.{u2} α (Distrib.toAdd.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_1))) a)) (bit0.{u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => β) a) (Distrib.toAdd.{u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => β) a) (NonUnitalNonAssocSemiring.toDistrib.{u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => β) a) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => β) a) _inst_2))) (FunLike.coe.{succ u1, succ u2, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => β) _x) (AddHomClass.toFunLike.{u1, u2, u3} F α β (Distrib.toAdd.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_1))) (Distrib.toAdd.{u3} β (NonUnitalNonAssocSemiring.toDistrib.{u3} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} β _inst_2))) _inst_3) f a))
Case conversion may be inaccurate. Consider using '#align map_bit0 map_bit0ₓ'. -/
/-- Additive homomorphisms preserve `bit0`. -/
@[simp]
theorem map_bit0 (f : F) (a : α) : (f (bit0 a) : β) = bit0 (f a) :=
  map_add _ _ _
#align map_bit0 map_bit0

end AddHomClass

namespace AddMonoidHom

#print AddMonoidHom.mulLeft /-
/-- Left multiplication by an element of a (semi)ring is an `add_monoid_hom` -/
def mulLeft {R : Type _} [NonUnitalNonAssocSemiring R] (r : R) : R →+ R
    where
  toFun := (· * ·) r
  map_zero' := mul_zero r
  map_add' := mul_add r
#align add_monoid_hom.mul_left AddMonoidHom.mulLeft
-/

/- warning: add_monoid_hom.coe_mul_left -> AddMonoidHom.coe_mul_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} R] (r : R), Eq.{succ u1} (R -> R) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, u1} R R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))) (fun (_x : AddMonoidHom.{u1, u1} R R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))) => R -> R) (AddMonoidHom.hasCoeToFun.{u1, u1} R R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))) (AddMonoidHom.mulLeft.{u1} R _inst_1 r)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R _inst_1))) r)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} R] (r : R), Eq.{succ u1} (forall (ᾰ : R), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : R) => R) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (AddMonoidHom.{u1, u1} R R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : R) => R) _x) (AddHomClass.toFunLike.{u1, u1, u1} (AddMonoidHom.{u1, u1} R R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))) R R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))) (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))) (AddMonoidHomClass.toAddHomClass.{u1, u1, u1} (AddMonoidHom.{u1, u1} R R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))) R R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoidHom.addMonoidHomClass.{u1, u1} R R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))))) (AddMonoidHom.mulLeft.{u1} R _inst_1 r)) (fun (x._@.Mathlib.Algebra.Ring.Basic._hyg.257 : R) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R _inst_1)) r x._@.Mathlib.Algebra.Ring.Basic._hyg.257)
Case conversion may be inaccurate. Consider using '#align add_monoid_hom.coe_mul_left AddMonoidHom.coe_mul_leftₓ'. -/
@[simp]
theorem coe_mul_left {R : Type _} [NonUnitalNonAssocSemiring R] (r : R) :
    ⇑(mulLeft r) = (· * ·) r :=
  rfl
#align add_monoid_hom.coe_mul_left AddMonoidHom.coe_mul_left

#print AddMonoidHom.mulRight /-
/-- Right multiplication by an element of a (semi)ring is an `add_monoid_hom` -/
def mulRight {R : Type _} [NonUnitalNonAssocSemiring R] (r : R) : R →+ R
    where
  toFun a := a * r
  map_zero' := zero_mul r
  map_add' _ _ := add_mul _ _ r
#align add_monoid_hom.mul_right AddMonoidHom.mulRight
-/

/- warning: add_monoid_hom.coe_mul_right -> AddMonoidHom.coe_mul_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} R] (r : R), Eq.{succ u1} (R -> R) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, u1} R R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))) (fun (_x : AddMonoidHom.{u1, u1} R R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))) => R -> R) (AddMonoidHom.hasCoeToFun.{u1, u1} R R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))) (AddMonoidHom.mulRight.{u1} R _inst_1 r)) (fun (_x : R) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R _inst_1))) _x r)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} R] (r : R), Eq.{succ u1} (forall (ᾰ : R), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : R) => R) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (AddMonoidHom.{u1, u1} R R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : R) => R) _x) (AddHomClass.toFunLike.{u1, u1, u1} (AddMonoidHom.{u1, u1} R R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))) R R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))) (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))) (AddMonoidHomClass.toAddHomClass.{u1, u1, u1} (AddMonoidHom.{u1, u1} R R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))) R R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoidHom.addMonoidHomClass.{u1, u1} R R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))))) (AddMonoidHom.mulRight.{u1} R _inst_1 r)) (fun (_x : R) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R _inst_1)) _x r)
Case conversion may be inaccurate. Consider using '#align add_monoid_hom.coe_mul_right AddMonoidHom.coe_mul_rightₓ'. -/
@[simp]
theorem coe_mul_right {R : Type _} [NonUnitalNonAssocSemiring R] (r : R) :
    ⇑(mulRight r) = (· * r) :=
  rfl
#align add_monoid_hom.coe_mul_right AddMonoidHom.coe_mul_right

/- warning: add_monoid_hom.mul_right_apply -> AddMonoidHom.mul_right_apply is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} R] (a : R) (r : R), Eq.{succ u1} R (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, u1} R R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))) (fun (_x : AddMonoidHom.{u1, u1} R R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))) => R -> R) (AddMonoidHom.hasCoeToFun.{u1, u1} R R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))) (AddMonoidHom.mulRight.{u1} R _inst_1 r) a) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R _inst_1))) a r)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} R] (a : R) (r : R), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : R) => R) a) (FunLike.coe.{succ u1, succ u1, succ u1} (AddMonoidHom.{u1, u1} R R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : R) => R) _x) (AddHomClass.toFunLike.{u1, u1, u1} (AddMonoidHom.{u1, u1} R R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))) R R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))) (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))) (AddMonoidHomClass.toAddHomClass.{u1, u1, u1} (AddMonoidHom.{u1, u1} R R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))) R R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoidHom.addMonoidHomClass.{u1, u1} R R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1))) (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R _inst_1)))))) (AddMonoidHom.mulRight.{u1} R _inst_1 r) a) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R _inst_1)) a r)
Case conversion may be inaccurate. Consider using '#align add_monoid_hom.mul_right_apply AddMonoidHom.mul_right_applyₓ'. -/
theorem mul_right_apply {R : Type _} [NonUnitalNonAssocSemiring R] (a r : R) :
    mulRight r a = a * r :=
  rfl
#align add_monoid_hom.mul_right_apply AddMonoidHom.mul_right_apply

end AddMonoidHom

section HasDistribNeg

section Mul

variable [Mul α] [HasDistribNeg α]

open MulOpposite

instance : HasDistribNeg αᵐᵒᵖ :=
  {
    MulOpposite.hasInvolutiveNeg
      _ with
    neg_mul := fun _ _ => unop_injective <| mul_neg _ _
    mul_neg := fun _ _ => unop_injective <| neg_mul _ _ }

end Mul

section Group

variable [Group α] [HasDistribNeg α]

/- warning: inv_neg' -> inv_neg' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))] (a : α), Eq.{succ u1} α (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) _inst_2)) a)) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) _inst_2)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))] (a : α), Eq.{succ u1} α (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) _inst_2)) a)) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) _inst_2)) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align inv_neg' inv_neg'ₓ'. -/
@[simp]
theorem inv_neg' (a : α) : (-a)⁻¹ = -a⁻¹ := by
  rw [eq_comm, eq_inv_iff_mul_eq_one, neg_mul, mul_neg, neg_neg, mul_left_inv]
#align inv_neg' inv_neg'

end Group

end HasDistribNeg

section NonUnitalCommRing

variable [NonUnitalCommRing α] {a b c : α}

attribute [local simp] add_assoc add_comm add_left_comm mul_comm

/- warning: Vieta_formula_quadratic -> vieta_formula_quadratic is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonUnitalCommRing.{u1} α] {b : α} {c : α} {x : α}, (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1)))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1)))))) x x) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1)))))) b x)) c) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1))))))))) -> (Exists.{succ u1} α (fun (y : α) => And (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1)))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1)))))) y y) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1)))))) b y)) c) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1))))))))) (And (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1)))))) x y) b) (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1)))))) x y) c))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonUnitalCommRing.{u1} α] {b : α} {c : α} {x : α}, (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1)))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1)))) x x) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1)))) b x)) c) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (SemigroupWithZero.toZero.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1))))))) -> (Exists.{succ u1} α (fun (y : α) => And (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1)))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1)))) y y) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1)))) b y)) c) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (SemigroupWithZero.toZero.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1))))))) (And (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1)))))) x y) b) (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1)))) x y) c))))
Case conversion may be inaccurate. Consider using '#align Vieta_formula_quadratic vieta_formula_quadraticₓ'. -/
/-- Vieta's formula for a quadratic equation, relating the coefficients of the polynomial with
  its roots. This particular version states that if we have a root `x` of a monic quadratic
  polynomial, then there is another root `y` such that `x + y` is negative the `a_1` coefficient
  and `x * y` is the `a_0` coefficient. -/
theorem vieta_formula_quadratic {b c x : α} (h : x * x - b * x + c = 0) :
    ∃ y : α, y * y - b * y + c = 0 ∧ x + y = b ∧ x * y = c :=
  by
  have : c = x * (b - x) := (eq_neg_of_add_eq_zero_right h).trans (by simp [mul_sub, mul_comm])
  refine' ⟨b - x, _, by simp, by rw [this]⟩
  rw [this, sub_add, ← sub_mul, sub_self]
#align Vieta_formula_quadratic vieta_formula_quadratic

end NonUnitalCommRing

/- warning: succ_ne_self -> succ_ne_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonAssocRing.{u1} α] [_inst_2 : Nontrivial.{u1} α] (a : α), Ne.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_1))))) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))))))) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonAssocRing.{u1} α] [_inst_2 : Nontrivial.{u1} α] (a : α), Ne.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_1))))) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (NonAssocRing.toOne.{u1} α _inst_1)))) a
Case conversion may be inaccurate. Consider using '#align succ_ne_self succ_ne_selfₓ'. -/
theorem succ_ne_self [NonAssocRing α] [Nontrivial α] (a : α) : a + 1 ≠ a := fun h =>
  one_ne_zero ((add_right_inj a).mp (by simp [h]))
#align succ_ne_self succ_ne_self

/- warning: pred_ne_self -> pred_ne_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonAssocRing.{u1} α] [_inst_2 : Nontrivial.{u1} α] (a : α), Ne.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))))) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))))))) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonAssocRing.{u1} α] [_inst_2 : Nontrivial.{u1} α] (a : α), Ne.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (AddGroupWithOne.toSub.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (NonAssocRing.toOne.{u1} α _inst_1)))) a
Case conversion may be inaccurate. Consider using '#align pred_ne_self pred_ne_selfₓ'. -/
theorem pred_ne_self [NonAssocRing α] [Nontrivial α] (a : α) : a - 1 ≠ a := fun h =>
  one_ne_zero (neg_injective ((add_right_inj a).mp (by simpa [sub_eq_add_neg] using h)))
#align pred_ne_self pred_ne_self

section NoZeroDivisors

variable (α)

/- warning: is_left_cancel_mul_zero.to_no_zero_divisors -> IsLeftCancelMulZero.to_noZeroDivisors is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Ring.{u1} α] [_inst_2 : IsLeftCancelMulZero.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α _inst_1)) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))], NoZeroDivisors.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α _inst_1)) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Ring.{u1} α] [_inst_2 : IsLeftCancelMulZero.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))) (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)))], NoZeroDivisors.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))) (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align is_left_cancel_mul_zero.to_no_zero_divisors IsLeftCancelMulZero.to_noZeroDivisorsₓ'. -/
theorem IsLeftCancelMulZero.to_noZeroDivisors [Ring α] [IsLeftCancelMulZero α] : NoZeroDivisors α :=
  by
  refine' ⟨fun x y h => _⟩
  by_cases hx : x = 0
  · left
    exact hx
  · right
    rw [← sub_zero (x * y), ← mul_zero x, ← mul_sub] at h
    convert IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hx h
    rw [sub_zero]
#align is_left_cancel_mul_zero.to_no_zero_divisors IsLeftCancelMulZero.to_noZeroDivisors

/- warning: is_right_cancel_mul_zero.to_no_zero_divisors -> IsRightCancelMulZero.to_noZeroDivisors is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Ring.{u1} α] [_inst_2 : IsRightCancelMulZero.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α _inst_1)) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))], NoZeroDivisors.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α _inst_1)) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Ring.{u1} α] [_inst_2 : IsRightCancelMulZero.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))) (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)))], NoZeroDivisors.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))) (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align is_right_cancel_mul_zero.to_no_zero_divisors IsRightCancelMulZero.to_noZeroDivisorsₓ'. -/
theorem IsRightCancelMulZero.to_noZeroDivisors [Ring α] [IsRightCancelMulZero α] :
    NoZeroDivisors α := by
  refine' ⟨fun x y h => _⟩
  by_cases hy : y = 0
  · right
    exact hy
  · left
    rw [← sub_zero (x * y), ← zero_mul y, ← sub_mul] at h
    convert IsRightCancelMulZero.mul_right_cancel_of_ne_zero hy h
    rw [sub_zero]
#align is_right_cancel_mul_zero.to_no_zero_divisors IsRightCancelMulZero.to_noZeroDivisors

/- warning: no_zero_divisors.to_is_cancel_mul_zero -> NoZeroDivisors.to_isCancelMulZero is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Ring.{u1} α] [_inst_2 : NoZeroDivisors.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α _inst_1)) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))], IsCancelMulZero.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α _inst_1)) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Ring.{u1} α] [_inst_2 : NoZeroDivisors.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))) (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)))], IsCancelMulZero.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))) (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align no_zero_divisors.to_is_cancel_mul_zero NoZeroDivisors.to_isCancelMulZeroₓ'. -/
instance (priority := 100) NoZeroDivisors.to_isCancelMulZero [Ring α] [NoZeroDivisors α] :
    IsCancelMulZero α
    where
  mul_left_cancel_of_ne_zero a b c ha h :=
    by
    rw [← sub_eq_zero, ← mul_sub] at h
    exact sub_eq_zero.1 ((eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_left ha)
  mul_right_cancel_of_ne_zero a b c hb h :=
    by
    rw [← sub_eq_zero, ← sub_mul] at h
    exact sub_eq_zero.1 ((eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_right hb)
#align no_zero_divisors.to_is_cancel_mul_zero NoZeroDivisors.to_isCancelMulZero

/- warning: no_zero_divisors.to_is_domain -> NoZeroDivisors.to_isDomain is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Ring.{u1} α] [h : Nontrivial.{u1} α] [_inst_2 : NoZeroDivisors.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α _inst_1)) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))], IsDomain.{u1} α (Ring.toSemiring.{u1} α _inst_1)
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Ring.{u1} α] [h : Nontrivial.{u1} α] [_inst_2 : NoZeroDivisors.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))) (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)))], IsDomain.{u1} α (Ring.toSemiring.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align no_zero_divisors.to_is_domain NoZeroDivisors.to_isDomainₓ'. -/
theorem NoZeroDivisors.to_isDomain [Ring α] [h : Nontrivial α] [NoZeroDivisors α] : IsDomain α :=
  { NoZeroDivisors.to_isCancelMulZero α, h with }
#align no_zero_divisors.to_is_domain NoZeroDivisors.to_isDomain

/- warning: is_domain.to_no_zero_divisors -> IsDomain.to_noZeroDivisors is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Ring.{u1} α] [_inst_2 : IsDomain.{u1} α (Ring.toSemiring.{u1} α _inst_1)], NoZeroDivisors.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α _inst_1)) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Ring.{u1} α] [_inst_2 : IsDomain.{u1} α (Ring.toSemiring.{u1} α _inst_1)], NoZeroDivisors.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))) (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align is_domain.to_no_zero_divisors IsDomain.to_noZeroDivisorsₓ'. -/
instance (priority := 100) IsDomain.to_noZeroDivisors [Ring α] [IsDomain α] : NoZeroDivisors α :=
  IsRightCancelMulZero.to_noZeroDivisors α
#align is_domain.to_no_zero_divisors IsDomain.to_noZeroDivisors

end NoZeroDivisors

