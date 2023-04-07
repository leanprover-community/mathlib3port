/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot

! This file was ported from Lean 3 source module topology.algebra.group.basic
! leanprover-community/mathlib commit 3b1890e71632be9e3b2086ab512c3259a7e9a3ef
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.GroupAction.ConjAct
import Mathbin.GroupTheory.GroupAction.Quotient
import Mathbin.GroupTheory.QuotientGroup
import Mathbin.Topology.Algebra.Monoid
import Mathbin.Topology.Algebra.Constructions

/-!
# Topological groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the following typeclasses:

* `topological_group`, `topological_add_group`: multiplicative and additive topological groups,
  i.e., groups with continuous `(*)` and `(⁻¹)` / `(+)` and `(-)`;

* `has_continuous_sub G` means that `G` has a continuous subtraction operation.

There is an instance deducing `has_continuous_sub` from `topological_group` but we use a separate
typeclass because, e.g., `ℕ` and `ℝ≥0` have continuous subtraction but are not additive groups.

We also define `homeomorph` versions of several `equiv`s: `homeomorph.mul_left`,
`homeomorph.mul_right`, `homeomorph.inv`, and prove a few facts about neighbourhood filters in
groups.

## Tags

topological space, group, topological group
-/


open Classical Set Filter TopologicalSpace Function

open Classical Topology Filter Pointwise

universe u v w x

variable {α : Type u} {β : Type v} {G : Type w} {H : Type x}

section ContinuousMulGroup

/-!
### Groups with continuous multiplication

In this section we prove a few statements about groups with continuous `(*)`.
-/


variable [TopologicalSpace G] [Group G] [ContinuousMul G]

/- warning: homeomorph.mul_left -> Homeomorph.mulLeft is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))], G -> (Homeomorph.{u1, u1} G G _inst_1 _inst_1)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))], G -> (Homeomorph.{u1, u1} G G _inst_1 _inst_1)
Case conversion may be inaccurate. Consider using '#align homeomorph.mul_left Homeomorph.mulLeftₓ'. -/
/-- Multiplication from the left in a topological group as a homeomorphism. -/
@[to_additive "Addition from the left in a topological additive group as a homeomorphism."]
protected def Homeomorph.mulLeft (a : G) : G ≃ₜ G :=
  { Equiv.mulLeft a with
    continuous_toFun := continuous_const.mul continuous_id
    continuous_invFun := continuous_const.mul continuous_id }
#align homeomorph.mul_left Homeomorph.mulLeft
#align homeomorph.add_left Homeomorph.addLeft

/- warning: homeomorph.coe_mul_left -> Homeomorph.coe_mulLeft is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] (a : G), Eq.{succ u1} (G -> G) (coeFn.{succ u1, succ u1} (Homeomorph.{u1, u1} G G _inst_1 _inst_1) (fun (_x : Homeomorph.{u1, u1} G G _inst_1 _inst_1) => G -> G) (Homeomorph.hasCoeToFun.{u1, u1} G G _inst_1 _inst_1) (Homeomorph.mulLeft.{u1} G _inst_1 _inst_2 _inst_3 a)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) a)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] (a : G), Eq.{succ u1} (G -> G) (FunLike.coe.{succ u1, succ u1, succ u1} (Homeomorph.{u1, u1} G G _inst_1 _inst_1) G (fun (_x : G) => G) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Homeomorph.{u1, u1} G G _inst_1 _inst_1) G G (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Homeomorph.{u1, u1} G G _inst_1 _inst_1) G G (Homeomorph.instEquivLikeHomeomorph.{u1, u1} G G _inst_1 _inst_1))) (Homeomorph.mulLeft.{u1} G _inst_1 _inst_2 _inst_3 a)) ((fun (x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.111 : G) (x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.113 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.111 x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.113) a)
Case conversion may be inaccurate. Consider using '#align homeomorph.coe_mul_left Homeomorph.coe_mulLeftₓ'. -/
@[simp, to_additive]
theorem Homeomorph.coe_mulLeft (a : G) : ⇑(Homeomorph.mulLeft a) = (· * ·) a :=
  rfl
#align homeomorph.coe_mul_left Homeomorph.coe_mulLeft
#align homeomorph.coe_add_left Homeomorph.coe_addLeft

/- warning: homeomorph.mul_left_symm -> Homeomorph.mulLeft_symm is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] (a : G), Eq.{succ u1} (Homeomorph.{u1, u1} G G _inst_1 _inst_1) (Homeomorph.symm.{u1, u1} G G _inst_1 _inst_1 (Homeomorph.mulLeft.{u1} G _inst_1 _inst_2 _inst_3 a)) (Homeomorph.mulLeft.{u1} G _inst_1 _inst_2 _inst_3 (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) a))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] (a : G), Eq.{succ u1} (Homeomorph.{u1, u1} G G _inst_1 _inst_1) (Homeomorph.symm.{u1, u1} G G _inst_1 _inst_1 (Homeomorph.mulLeft.{u1} G _inst_1 _inst_2 _inst_3 a)) (Homeomorph.mulLeft.{u1} G _inst_1 _inst_2 _inst_3 (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))) a))
Case conversion may be inaccurate. Consider using '#align homeomorph.mul_left_symm Homeomorph.mulLeft_symmₓ'. -/
@[to_additive]
theorem Homeomorph.mulLeft_symm (a : G) : (Homeomorph.mulLeft a).symm = Homeomorph.mulLeft a⁻¹ :=
  by
  ext
  rfl
#align homeomorph.mul_left_symm Homeomorph.mulLeft_symm
#align homeomorph.add_left_symm Homeomorph.addLeft_symm

/- warning: is_open_map_mul_left -> isOpenMap_mul_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] (a : G), IsOpenMap.{u1, u1} G G _inst_1 _inst_1 (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) a x)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] (a : G), IsOpenMap.{u1, u1} G G _inst_1 _inst_1 (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) a x)
Case conversion may be inaccurate. Consider using '#align is_open_map_mul_left isOpenMap_mul_leftₓ'. -/
@[to_additive]
theorem isOpenMap_mul_left (a : G) : IsOpenMap fun x => a * x :=
  (Homeomorph.mulLeft a).IsOpenMap
#align is_open_map_mul_left isOpenMap_mul_left
#align is_open_map_add_left isOpenMap_add_left

/- warning: is_open.left_coset -> IsOpen.leftCoset is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] {U : Set.{u1} G}, (IsOpen.{u1} G _inst_1 U) -> (forall (x : G), IsOpen.{u1} G _inst_1 (leftCoset.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) x U))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] {U : Set.{u1} G}, (IsOpen.{u1} G _inst_1 U) -> (forall (x : G), IsOpen.{u1} G _inst_1 (leftCoset.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) x U))
Case conversion may be inaccurate. Consider using '#align is_open.left_coset IsOpen.leftCosetₓ'. -/
@[to_additive IsOpen.left_add_coset]
theorem IsOpen.leftCoset {U : Set G} (h : IsOpen U) (x : G) : IsOpen (leftCoset x U) :=
  isOpenMap_mul_left x _ h
#align is_open.left_coset IsOpen.leftCoset
#align is_open.left_add_coset IsOpen.left_add_coset

/- warning: is_closed_map_mul_left -> isClosedMap_mul_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] (a : G), IsClosedMap.{u1, u1} G G _inst_1 _inst_1 (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) a x)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] (a : G), IsClosedMap.{u1, u1} G G _inst_1 _inst_1 (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) a x)
Case conversion may be inaccurate. Consider using '#align is_closed_map_mul_left isClosedMap_mul_leftₓ'. -/
@[to_additive]
theorem isClosedMap_mul_left (a : G) : IsClosedMap fun x => a * x :=
  (Homeomorph.mulLeft a).IsClosedMap
#align is_closed_map_mul_left isClosedMap_mul_left
#align is_closed_map_add_left isClosedMap_add_left

/- warning: is_closed.left_coset -> IsClosed.leftCoset is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] {U : Set.{u1} G}, (IsClosed.{u1} G _inst_1 U) -> (forall (x : G), IsClosed.{u1} G _inst_1 (leftCoset.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) x U))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] {U : Set.{u1} G}, (IsClosed.{u1} G _inst_1 U) -> (forall (x : G), IsClosed.{u1} G _inst_1 (leftCoset.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) x U))
Case conversion may be inaccurate. Consider using '#align is_closed.left_coset IsClosed.leftCosetₓ'. -/
@[to_additive IsClosed.left_add_coset]
theorem IsClosed.leftCoset {U : Set G} (h : IsClosed U) (x : G) : IsClosed (leftCoset x U) :=
  isClosedMap_mul_left x _ h
#align is_closed.left_coset IsClosed.leftCoset
#align is_closed.left_add_coset IsClosed.left_add_coset

/- warning: homeomorph.mul_right -> Homeomorph.mulRight is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))], G -> (Homeomorph.{u1, u1} G G _inst_1 _inst_1)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))], G -> (Homeomorph.{u1, u1} G G _inst_1 _inst_1)
Case conversion may be inaccurate. Consider using '#align homeomorph.mul_right Homeomorph.mulRightₓ'. -/
/-- Multiplication from the right in a topological group as a homeomorphism. -/
@[to_additive "Addition from the right in a topological additive group as a homeomorphism."]
protected def Homeomorph.mulRight (a : G) : G ≃ₜ G :=
  { Equiv.mulRight a with
    continuous_toFun := continuous_id.mul continuous_const
    continuous_invFun := continuous_id.mul continuous_const }
#align homeomorph.mul_right Homeomorph.mulRight
#align homeomorph.add_right Homeomorph.addRight

/- warning: homeomorph.coe_mul_right -> Homeomorph.coe_mulRight is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] (a : G), Eq.{succ u1} (G -> G) (coeFn.{succ u1, succ u1} (Homeomorph.{u1, u1} G G _inst_1 _inst_1) (fun (_x : Homeomorph.{u1, u1} G G _inst_1 _inst_1) => G -> G) (Homeomorph.hasCoeToFun.{u1, u1} G G _inst_1 _inst_1) (Homeomorph.mulRight.{u1} G _inst_1 _inst_2 _inst_3 a)) (fun (g : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) g a)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] (a : G), Eq.{succ u1} (G -> G) (FunLike.coe.{succ u1, succ u1, succ u1} (Homeomorph.{u1, u1} G G _inst_1 _inst_1) G (fun (_x : G) => G) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Homeomorph.{u1, u1} G G _inst_1 _inst_1) G G (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Homeomorph.{u1, u1} G G _inst_1 _inst_1) G G (Homeomorph.instEquivLikeHomeomorph.{u1, u1} G G _inst_1 _inst_1))) (Homeomorph.mulRight.{u1} G _inst_1 _inst_2 _inst_3 a)) (fun (g : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) g a)
Case conversion may be inaccurate. Consider using '#align homeomorph.coe_mul_right Homeomorph.coe_mulRightₓ'. -/
@[simp, to_additive]
theorem Homeomorph.coe_mulRight (a : G) : ⇑(Homeomorph.mulRight a) = fun g => g * a :=
  rfl
#align homeomorph.coe_mul_right Homeomorph.coe_mulRight
#align homeomorph.coe_add_right Homeomorph.coe_addRight

/- warning: homeomorph.mul_right_symm -> Homeomorph.mulRight_symm is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] (a : G), Eq.{succ u1} (Homeomorph.{u1, u1} G G _inst_1 _inst_1) (Homeomorph.symm.{u1, u1} G G _inst_1 _inst_1 (Homeomorph.mulRight.{u1} G _inst_1 _inst_2 _inst_3 a)) (Homeomorph.mulRight.{u1} G _inst_1 _inst_2 _inst_3 (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) a))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] (a : G), Eq.{succ u1} (Homeomorph.{u1, u1} G G _inst_1 _inst_1) (Homeomorph.symm.{u1, u1} G G _inst_1 _inst_1 (Homeomorph.mulRight.{u1} G _inst_1 _inst_2 _inst_3 a)) (Homeomorph.mulRight.{u1} G _inst_1 _inst_2 _inst_3 (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))) a))
Case conversion may be inaccurate. Consider using '#align homeomorph.mul_right_symm Homeomorph.mulRight_symmₓ'. -/
@[to_additive]
theorem Homeomorph.mulRight_symm (a : G) : (Homeomorph.mulRight a).symm = Homeomorph.mulRight a⁻¹ :=
  by
  ext
  rfl
#align homeomorph.mul_right_symm Homeomorph.mulRight_symm
#align homeomorph.add_right_symm Homeomorph.addRight_symm

/- warning: is_open_map_mul_right -> isOpenMap_mul_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] (a : G), IsOpenMap.{u1, u1} G G _inst_1 _inst_1 (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) x a)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] (a : G), IsOpenMap.{u1, u1} G G _inst_1 _inst_1 (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) x a)
Case conversion may be inaccurate. Consider using '#align is_open_map_mul_right isOpenMap_mul_rightₓ'. -/
@[to_additive]
theorem isOpenMap_mul_right (a : G) : IsOpenMap fun x => x * a :=
  (Homeomorph.mulRight a).IsOpenMap
#align is_open_map_mul_right isOpenMap_mul_right
#align is_open_map_add_right isOpenMap_add_right

/- warning: is_open.right_coset -> IsOpen.rightCoset is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] {U : Set.{u1} G}, (IsOpen.{u1} G _inst_1 U) -> (forall (x : G), IsOpen.{u1} G _inst_1 (rightCoset.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) U x))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] {U : Set.{u1} G}, (IsOpen.{u1} G _inst_1 U) -> (forall (x : G), IsOpen.{u1} G _inst_1 (rightCoset.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) U x))
Case conversion may be inaccurate. Consider using '#align is_open.right_coset IsOpen.rightCosetₓ'. -/
@[to_additive IsOpen.right_add_coset]
theorem IsOpen.rightCoset {U : Set G} (h : IsOpen U) (x : G) : IsOpen (rightCoset U x) :=
  isOpenMap_mul_right x _ h
#align is_open.right_coset IsOpen.rightCoset
#align is_open.right_add_coset IsOpen.right_add_coset

/- warning: is_closed_map_mul_right -> isClosedMap_mul_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] (a : G), IsClosedMap.{u1, u1} G G _inst_1 _inst_1 (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) x a)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] (a : G), IsClosedMap.{u1, u1} G G _inst_1 _inst_1 (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) x a)
Case conversion may be inaccurate. Consider using '#align is_closed_map_mul_right isClosedMap_mul_rightₓ'. -/
@[to_additive]
theorem isClosedMap_mul_right (a : G) : IsClosedMap fun x => x * a :=
  (Homeomorph.mulRight a).IsClosedMap
#align is_closed_map_mul_right isClosedMap_mul_right
#align is_closed_map_add_right isClosedMap_add_right

/- warning: is_closed.right_coset -> IsClosed.rightCoset is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] {U : Set.{u1} G}, (IsClosed.{u1} G _inst_1 U) -> (forall (x : G), IsClosed.{u1} G _inst_1 (rightCoset.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) U x))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] {U : Set.{u1} G}, (IsClosed.{u1} G _inst_1 U) -> (forall (x : G), IsClosed.{u1} G _inst_1 (rightCoset.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) U x))
Case conversion may be inaccurate. Consider using '#align is_closed.right_coset IsClosed.rightCosetₓ'. -/
@[to_additive IsClosed.right_add_coset]
theorem IsClosed.rightCoset {U : Set G} (h : IsClosed U) (x : G) : IsClosed (rightCoset U x) :=
  isClosedMap_mul_right x _ h
#align is_closed.right_coset IsClosed.rightCoset
#align is_closed.right_add_coset IsClosed.right_add_coset

/- warning: discrete_topology_of_open_singleton_one -> discreteTopology_of_open_singleton_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))], (IsOpen.{u1} G _inst_1 (Singleton.singleton.{u1, u1} G (Set.{u1} G) (Set.hasSingleton.{u1} G) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))))))) -> (DiscreteTopology.{u1} G _inst_1)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))], (IsOpen.{u1} G _inst_1 (Singleton.singleton.{u1, u1} G (Set.{u1} G) (Set.instSingletonSet.{u1} G) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))))))) -> (DiscreteTopology.{u1} G _inst_1)
Case conversion may be inaccurate. Consider using '#align discrete_topology_of_open_singleton_one discreteTopology_of_open_singleton_oneₓ'. -/
@[to_additive]
theorem discreteTopology_of_open_singleton_one (h : IsOpen ({1} : Set G)) : DiscreteTopology G :=
  by
  rw [← singletons_open_iff_discrete]
  intro g
  suffices {g} = (fun x : G => g⁻¹ * x) ⁻¹' {1}
    by
    rw [this]
    exact (continuous_mul_left g⁻¹).isOpen_preimage _ h
  simp only [mul_one, Set.preimage_mul_left_singleton, eq_self_iff_true, inv_inv,
    Set.singleton_eq_singleton_iff]
#align discrete_topology_of_open_singleton_one discreteTopology_of_open_singleton_one
#align discrete_topology_of_open_singleton_zero discreteTopology_of_open_singleton_zero

/- warning: discrete_topology_iff_open_singleton_one -> discreteTopology_iff_open_singleton_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))], Iff (DiscreteTopology.{u1} G _inst_1) (IsOpen.{u1} G _inst_1 (Singleton.singleton.{u1, u1} G (Set.{u1} G) (Set.hasSingleton.{u1} G) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))], Iff (DiscreteTopology.{u1} G _inst_1) (IsOpen.{u1} G _inst_1 (Singleton.singleton.{u1, u1} G (Set.{u1} G) (Set.instSingletonSet.{u1} G) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align discrete_topology_iff_open_singleton_one discreteTopology_iff_open_singleton_oneₓ'. -/
@[to_additive]
theorem discreteTopology_iff_open_singleton_one : DiscreteTopology G ↔ IsOpen ({1} : Set G) :=
  ⟨fun h => forall_open_iff_discrete.mpr h {1}, discreteTopology_of_open_singleton_one⟩
#align discrete_topology_iff_open_singleton_one discreteTopology_iff_open_singleton_one
#align discrete_topology_iff_open_singleton_zero discreteTopology_iff_open_singleton_zero

end ContinuousMulGroup

/-!
### `has_continuous_inv` and `has_continuous_neg`
-/


#print ContinuousNeg /-
/-- Basic hypothesis to talk about a topological additive group. A topological additive group
over `M`, for example, is obtained by requiring the instances `add_group M` and
`has_continuous_add M` and `has_continuous_neg M`. -/
class ContinuousNeg (G : Type u) [TopologicalSpace G] [Neg G] : Prop where
  continuous_neg : Continuous fun a : G => -a
#align has_continuous_neg ContinuousNeg
-/

#print ContinuousInv /-
/-- Basic hypothesis to talk about a topological group. A topological group over `M`, for example,
is obtained by requiring the instances `group M` and `has_continuous_mul M` and
`has_continuous_inv M`. -/
@[to_additive]
class ContinuousInv (G : Type u) [TopologicalSpace G] [Inv G] : Prop where
  continuous_inv : Continuous fun a : G => a⁻¹
#align has_continuous_inv ContinuousInv
#align has_continuous_neg ContinuousNeg
-/

export ContinuousInv (continuous_inv)

export ContinuousNeg (continuous_neg)

section ContinuousInv

variable [TopologicalSpace G] [Inv G] [ContinuousInv G]

#print continuousOn_inv /-
@[to_additive]
theorem continuousOn_inv {s : Set G} : ContinuousOn Inv.inv s :=
  continuous_inv.ContinuousOn
#align continuous_on_inv continuousOn_inv
#align continuous_on_neg continuousOn_neg
-/

#print continuousWithinAt_inv /-
@[to_additive]
theorem continuousWithinAt_inv {s : Set G} {x : G} : ContinuousWithinAt Inv.inv s x :=
  continuous_inv.ContinuousWithinAt
#align continuous_within_at_inv continuousWithinAt_inv
#align continuous_within_at_neg continuousWithinAt_neg
-/

#print continuousAt_inv /-
@[to_additive]
theorem continuousAt_inv {x : G} : ContinuousAt Inv.inv x :=
  continuous_inv.ContinuousAt
#align continuous_at_inv continuousAt_inv
#align continuous_at_neg continuousAt_neg
-/

#print tendsto_inv /-
@[to_additive]
theorem tendsto_inv (a : G) : Tendsto Inv.inv (𝓝 a) (𝓝 a⁻¹) :=
  continuousAt_inv
#align tendsto_inv tendsto_inv
#align tendsto_neg tendsto_neg
-/

#print Filter.Tendsto.inv /-
/-- If a function converges to a value in a multiplicative topological group, then its inverse
converges to the inverse of this value. For the version in normed fields assuming additionally
that the limit is nonzero, use `tendsto.inv'`. -/
@[to_additive
      "If a function converges to a value in an additive topological group, then its\nnegation converges to the negation of this value."]
theorem Filter.Tendsto.inv {f : α → G} {l : Filter α} {y : G} (h : Tendsto f l (𝓝 y)) :
    Tendsto (fun x => (f x)⁻¹) l (𝓝 y⁻¹) :=
  (continuous_inv.Tendsto y).comp h
#align filter.tendsto.inv Filter.Tendsto.inv
#align filter.tendsto.neg Filter.Tendsto.neg
-/

variable [TopologicalSpace α] {f : α → G} {s : Set α} {x : α}

#print Continuous.inv /-
@[continuity, to_additive]
theorem Continuous.inv (hf : Continuous f) : Continuous fun x => (f x)⁻¹ :=
  continuous_inv.comp hf
#align continuous.inv Continuous.inv
#align continuous.neg Continuous.neg
-/

#print ContinuousAt.inv /-
@[to_additive]
theorem ContinuousAt.inv (hf : ContinuousAt f x) : ContinuousAt (fun x => (f x)⁻¹) x :=
  continuousAt_inv.comp hf
#align continuous_at.inv ContinuousAt.inv
#align continuous_at.neg ContinuousAt.neg
-/

#print ContinuousOn.inv /-
@[to_additive]
theorem ContinuousOn.inv (hf : ContinuousOn f s) : ContinuousOn (fun x => (f x)⁻¹) s :=
  continuous_inv.comp_continuousOn hf
#align continuous_on.inv ContinuousOn.inv
#align continuous_on.neg ContinuousOn.neg
-/

#print ContinuousWithinAt.inv /-
@[to_additive]
theorem ContinuousWithinAt.inv (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun x => (f x)⁻¹) s x :=
  hf.inv
#align continuous_within_at.inv ContinuousWithinAt.inv
#align continuous_within_at.neg ContinuousWithinAt.neg
-/

@[to_additive]
instance [TopologicalSpace H] [Inv H] [ContinuousInv H] : ContinuousInv (G × H) :=
  ⟨continuous_inv.fst'.prod_mk continuous_inv.snd'⟩

variable {ι : Type _}

#print Pi.continuousInv /-
@[to_additive]
instance Pi.continuousInv {C : ι → Type _} [∀ i, TopologicalSpace (C i)] [∀ i, Inv (C i)]
    [∀ i, ContinuousInv (C i)] : ContinuousInv (∀ i, C i)
    where continuous_inv := continuous_pi fun i => (continuous_apply i).inv
#align pi.has_continuous_inv Pi.continuousInv
#align pi.has_continuous_neg Pi.continuousNeg
-/

#print Pi.has_continuous_inv' /-
/-- A version of `pi.has_continuous_inv` for non-dependent functions. It is needed because sometimes
Lean fails to use `pi.has_continuous_inv` for non-dependent functions. -/
@[to_additive
      "A version of `pi.has_continuous_neg` for non-dependent functions. It is needed\nbecause sometimes Lean fails to use `pi.has_continuous_neg` for non-dependent functions."]
instance Pi.has_continuous_inv' : ContinuousInv (ι → G) :=
  Pi.continuousInv
#align pi.has_continuous_inv' Pi.has_continuous_inv'
#align pi.has_continuous_neg' Pi.has_continuous_neg'
-/

#print continuousInv_of_discreteTopology /-
@[to_additive]
instance (priority := 100) continuousInv_of_discreteTopology [TopologicalSpace H] [Inv H]
    [DiscreteTopology H] : ContinuousInv H :=
  ⟨continuous_of_discreteTopology⟩
#align has_continuous_inv_of_discrete_topology continuousInv_of_discreteTopology
#align has_continuous_neg_of_discrete_topology continuousNeg_of_discreteTopology
-/

section PointwiseLimits

variable (G₁ G₂ : Type _) [TopologicalSpace G₂] [T2Space G₂]

/- warning: is_closed_set_of_map_inv -> isClosed_setOf_map_inv is a dubious translation:
lean 3 declaration is
  forall (G₁ : Type.{u1}) (G₂ : Type.{u2}) [_inst_5 : TopologicalSpace.{u2} G₂] [_inst_6 : T2Space.{u2} G₂ _inst_5] [_inst_7 : Inv.{u1} G₁] [_inst_8 : Inv.{u2} G₂] [_inst_9 : ContinuousInv.{u2} G₂ _inst_5 _inst_8], IsClosed.{max u1 u2} (G₁ -> G₂) (Pi.topologicalSpace.{u1, u2} G₁ (fun (ᾰ : G₁) => G₂) (fun (a : G₁) => _inst_5)) (setOf.{max u1 u2} (G₁ -> G₂) (fun (f : G₁ -> G₂) => forall (x : G₁), Eq.{succ u2} G₂ (f (Inv.inv.{u1} G₁ _inst_7 x)) (Inv.inv.{u2} G₂ _inst_8 (f x))))
but is expected to have type
  forall (G₁ : Type.{u2}) (G₂ : Type.{u1}) [_inst_5 : TopologicalSpace.{u1} G₂] [_inst_6 : T2Space.{u1} G₂ _inst_5] [_inst_7 : Inv.{u2} G₁] [_inst_8 : Inv.{u1} G₂] [_inst_9 : ContinuousInv.{u1} G₂ _inst_5 _inst_8], IsClosed.{max u2 u1} (G₁ -> G₂) (Pi.topologicalSpace.{u2, u1} G₁ (fun (ᾰ : G₁) => G₂) (fun (a : G₁) => _inst_5)) (setOf.{max u2 u1} (G₁ -> G₂) (fun (f : G₁ -> G₂) => forall (x : G₁), Eq.{succ u1} G₂ (f (Inv.inv.{u2} G₁ _inst_7 x)) (Inv.inv.{u1} G₂ _inst_8 (f x))))
Case conversion may be inaccurate. Consider using '#align is_closed_set_of_map_inv isClosed_setOf_map_invₓ'. -/
@[to_additive]
theorem isClosed_setOf_map_inv [Inv G₁] [Inv G₂] [ContinuousInv G₂] :
    IsClosed { f : G₁ → G₂ | ∀ x, f x⁻¹ = (f x)⁻¹ } :=
  by
  simp only [set_of_forall]
  refine' isClosed_interᵢ fun i => isClosed_eq (continuous_apply _) (continuous_apply _).inv
#align is_closed_set_of_map_inv isClosed_setOf_map_inv
#align is_closed_set_of_map_neg isClosed_setOf_map_neg

end PointwiseLimits

instance [TopologicalSpace H] [Inv H] [ContinuousInv H] : ContinuousNeg (Additive H)
    where continuous_neg := @continuous_inv H _ _ _

instance [TopologicalSpace H] [Neg H] [ContinuousNeg H] : ContinuousInv (Multiplicative H)
    where continuous_inv := @continuous_neg H _ _ _

end ContinuousInv

section ContinuousInvolutiveInv

variable [TopologicalSpace G] [InvolutiveInv G] [ContinuousInv G] {s : Set G}

/- warning: is_compact.inv -> IsCompact.inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : InvolutiveInv.{u1} G] [_inst_3 : ContinuousInv.{u1} G _inst_1 (InvolutiveInv.toHasInv.{u1} G _inst_2)] {s : Set.{u1} G}, (IsCompact.{u1} G _inst_1 s) -> (IsCompact.{u1} G _inst_1 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_2)) s))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : InvolutiveInv.{u1} G] [_inst_3 : ContinuousInv.{u1} G _inst_1 (InvolutiveInv.toInv.{u1} G _inst_2)] {s : Set.{u1} G}, (IsCompact.{u1} G _inst_1 s) -> (IsCompact.{u1} G _inst_1 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_2)) s))
Case conversion may be inaccurate. Consider using '#align is_compact.inv IsCompact.invₓ'. -/
@[to_additive]
theorem IsCompact.inv (hs : IsCompact s) : IsCompact s⁻¹ :=
  by
  rw [← image_inv]
  exact hs.image continuous_inv
#align is_compact.inv IsCompact.inv
#align is_compact.neg IsCompact.neg

variable (G)

/- warning: homeomorph.inv -> Homeomorph.inv is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_4 : TopologicalSpace.{u1} G] [_inst_5 : InvolutiveInv.{u1} G] [_inst_6 : ContinuousInv.{u1} G _inst_4 (InvolutiveInv.toHasInv.{u1} G _inst_5)], Homeomorph.{u1, u1} G G _inst_4 _inst_4
but is expected to have type
  forall (G : Type.{u1}) [_inst_4 : TopologicalSpace.{u1} G] [_inst_5 : InvolutiveInv.{u1} G] [_inst_6 : ContinuousInv.{u1} G _inst_4 (InvolutiveInv.toInv.{u1} G _inst_5)], Homeomorph.{u1, u1} G G _inst_4 _inst_4
Case conversion may be inaccurate. Consider using '#align homeomorph.inv Homeomorph.invₓ'. -/
/-- Inversion in a topological group as a homeomorphism. -/
@[to_additive "Negation in a topological group as a homeomorphism."]
protected def Homeomorph.inv (G : Type _) [TopologicalSpace G] [InvolutiveInv G] [ContinuousInv G] :
    G ≃ₜ G :=
  { Equiv.inv G with
    continuous_toFun := continuous_inv
    continuous_invFun := continuous_inv }
#align homeomorph.inv Homeomorph.inv
#align homeomorph.neg Homeomorph.neg

/- warning: is_open_map_inv -> isOpenMap_inv is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : InvolutiveInv.{u1} G] [_inst_3 : ContinuousInv.{u1} G _inst_1 (InvolutiveInv.toHasInv.{u1} G _inst_2)], IsOpenMap.{u1, u1} G G _inst_1 _inst_1 (Inv.inv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_2))
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : InvolutiveInv.{u1} G] [_inst_3 : ContinuousInv.{u1} G _inst_1 (InvolutiveInv.toInv.{u1} G _inst_2)], IsOpenMap.{u1, u1} G G _inst_1 _inst_1 (Inv.inv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_2))
Case conversion may be inaccurate. Consider using '#align is_open_map_inv isOpenMap_invₓ'. -/
@[to_additive]
theorem isOpenMap_inv : IsOpenMap (Inv.inv : G → G) :=
  (Homeomorph.inv _).IsOpenMap
#align is_open_map_inv isOpenMap_inv
#align is_open_map_neg isOpenMap_neg

/- warning: is_closed_map_inv -> isClosedMap_inv is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : InvolutiveInv.{u1} G] [_inst_3 : ContinuousInv.{u1} G _inst_1 (InvolutiveInv.toHasInv.{u1} G _inst_2)], IsClosedMap.{u1, u1} G G _inst_1 _inst_1 (Inv.inv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_2))
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : InvolutiveInv.{u1} G] [_inst_3 : ContinuousInv.{u1} G _inst_1 (InvolutiveInv.toInv.{u1} G _inst_2)], IsClosedMap.{u1, u1} G G _inst_1 _inst_1 (Inv.inv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_2))
Case conversion may be inaccurate. Consider using '#align is_closed_map_inv isClosedMap_invₓ'. -/
@[to_additive]
theorem isClosedMap_inv : IsClosedMap (Inv.inv : G → G) :=
  (Homeomorph.inv _).IsClosedMap
#align is_closed_map_inv isClosedMap_inv
#align is_closed_map_neg isClosedMap_neg

variable {G}

/- warning: is_open.inv -> IsOpen.inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : InvolutiveInv.{u1} G] [_inst_3 : ContinuousInv.{u1} G _inst_1 (InvolutiveInv.toHasInv.{u1} G _inst_2)] {s : Set.{u1} G}, (IsOpen.{u1} G _inst_1 s) -> (IsOpen.{u1} G _inst_1 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_2)) s))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : InvolutiveInv.{u1} G] [_inst_3 : ContinuousInv.{u1} G _inst_1 (InvolutiveInv.toInv.{u1} G _inst_2)] {s : Set.{u1} G}, (IsOpen.{u1} G _inst_1 s) -> (IsOpen.{u1} G _inst_1 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_2)) s))
Case conversion may be inaccurate. Consider using '#align is_open.inv IsOpen.invₓ'. -/
@[to_additive]
theorem IsOpen.inv (hs : IsOpen s) : IsOpen s⁻¹ :=
  hs.Preimage continuous_inv
#align is_open.inv IsOpen.inv
#align is_open.neg IsOpen.neg

/- warning: is_closed.inv -> IsClosed.inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : InvolutiveInv.{u1} G] [_inst_3 : ContinuousInv.{u1} G _inst_1 (InvolutiveInv.toHasInv.{u1} G _inst_2)] {s : Set.{u1} G}, (IsClosed.{u1} G _inst_1 s) -> (IsClosed.{u1} G _inst_1 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_2)) s))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : InvolutiveInv.{u1} G] [_inst_3 : ContinuousInv.{u1} G _inst_1 (InvolutiveInv.toInv.{u1} G _inst_2)] {s : Set.{u1} G}, (IsClosed.{u1} G _inst_1 s) -> (IsClosed.{u1} G _inst_1 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_2)) s))
Case conversion may be inaccurate. Consider using '#align is_closed.inv IsClosed.invₓ'. -/
@[to_additive]
theorem IsClosed.inv (hs : IsClosed s) : IsClosed s⁻¹ :=
  hs.Preimage continuous_inv
#align is_closed.inv IsClosed.inv
#align is_closed.neg IsClosed.neg

/- warning: inv_closure -> inv_closure is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : InvolutiveInv.{u1} G] [_inst_3 : ContinuousInv.{u1} G _inst_1 (InvolutiveInv.toHasInv.{u1} G _inst_2)] (s : Set.{u1} G), Eq.{succ u1} (Set.{u1} G) (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_2)) (closure.{u1} G _inst_1 s)) (closure.{u1} G _inst_1 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_2)) s))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : InvolutiveInv.{u1} G] [_inst_3 : ContinuousInv.{u1} G _inst_1 (InvolutiveInv.toInv.{u1} G _inst_2)] (s : Set.{u1} G), Eq.{succ u1} (Set.{u1} G) (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_2)) (closure.{u1} G _inst_1 s)) (closure.{u1} G _inst_1 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_2)) s))
Case conversion may be inaccurate. Consider using '#align inv_closure inv_closureₓ'. -/
@[to_additive]
theorem inv_closure : ∀ s : Set G, (closure s)⁻¹ = closure s⁻¹ :=
  (Homeomorph.inv G).preimage_closure
#align inv_closure inv_closure
#align neg_closure neg_closure

end ContinuousInvolutiveInv

section LatticeOps

variable {ι' : Sort _} [Inv G]

/- warning: has_continuous_inv_Inf -> continuousInv_infₛ is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Inv.{u1} G] {ts : Set.{u1} (TopologicalSpace.{u1} G)}, (forall (t : TopologicalSpace.{u1} G), (Membership.Mem.{u1, u1} (TopologicalSpace.{u1} G) (Set.{u1} (TopologicalSpace.{u1} G)) (Set.hasMem.{u1} (TopologicalSpace.{u1} G)) t ts) -> (ContinuousInv.{u1} G t _inst_1)) -> (ContinuousInv.{u1} G (InfSet.infₛ.{u1} (TopologicalSpace.{u1} G) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.{u1} G) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} G) (TopologicalSpace.completeLattice.{u1} G))) ts) _inst_1)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Inv.{u1} G] {ts : Set.{u1} (TopologicalSpace.{u1} G)}, (forall (t : TopologicalSpace.{u1} G), (Membership.mem.{u1, u1} (TopologicalSpace.{u1} G) (Set.{u1} (TopologicalSpace.{u1} G)) (Set.instMembershipSet.{u1} (TopologicalSpace.{u1} G)) t ts) -> (ContinuousInv.{u1} G t _inst_1)) -> (ContinuousInv.{u1} G (InfSet.infₛ.{u1} (TopologicalSpace.{u1} G) (ConditionallyCompleteLattice.toInfSet.{u1} (TopologicalSpace.{u1} G) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} G) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} G))) ts) _inst_1)
Case conversion may be inaccurate. Consider using '#align has_continuous_inv_Inf continuousInv_infₛₓ'. -/
@[to_additive]
theorem continuousInv_infₛ {ts : Set (TopologicalSpace G)} (h : ∀ t ∈ ts, @ContinuousInv G t _) :
    @ContinuousInv G (infₛ ts) _ :=
  {
    continuous_inv :=
      continuous_infₛ_rng.2 fun t ht =>
        continuous_infₛ_dom ht (@ContinuousInv.continuous_inv G t _ (h t ht)) }
#align has_continuous_inv_Inf continuousInv_infₛ
#align has_continuous_neg_Inf continuousNeg_infₛ

/- warning: has_continuous_inv_infi -> continuousInv_infᵢ is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {ι' : Sort.{u2}} [_inst_1 : Inv.{u1} G] {ts' : ι' -> (TopologicalSpace.{u1} G)}, (forall (i : ι'), ContinuousInv.{u1} G (ts' i) _inst_1) -> (ContinuousInv.{u1} G (infᵢ.{u1, u2} (TopologicalSpace.{u1} G) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.{u1} G) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} G) (TopologicalSpace.completeLattice.{u1} G))) ι' (fun (i : ι') => ts' i)) _inst_1)
but is expected to have type
  forall {G : Type.{u2}} {ι' : Sort.{u1}} [_inst_1 : Inv.{u2} G] {ts' : ι' -> (TopologicalSpace.{u2} G)}, (forall (i : ι'), ContinuousInv.{u2} G (ts' i) _inst_1) -> (ContinuousInv.{u2} G (infᵢ.{u2, u1} (TopologicalSpace.{u2} G) (ConditionallyCompleteLattice.toInfSet.{u2} (TopologicalSpace.{u2} G) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} G) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u2} G))) ι' (fun (i : ι') => ts' i)) _inst_1)
Case conversion may be inaccurate. Consider using '#align has_continuous_inv_infi continuousInv_infᵢₓ'. -/
@[to_additive]
theorem continuousInv_infᵢ {ts' : ι' → TopologicalSpace G} (h' : ∀ i, @ContinuousInv G (ts' i) _) :
    @ContinuousInv G (⨅ i, ts' i) _ := by
  rw [← infₛ_range]
  exact continuousInv_infₛ (set.forall_range_iff.mpr h')
#align has_continuous_inv_infi continuousInv_infᵢ
#align has_continuous_neg_infi continuousNeg_infᵢ

/- warning: has_continuous_inv_inf -> continuousInv_inf is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Inv.{u1} G] {t₁ : TopologicalSpace.{u1} G} {t₂ : TopologicalSpace.{u1} G}, (ContinuousInv.{u1} G t₁ _inst_1) -> (ContinuousInv.{u1} G t₂ _inst_1) -> (ContinuousInv.{u1} G (Inf.inf.{u1} (TopologicalSpace.{u1} G) (SemilatticeInf.toHasInf.{u1} (TopologicalSpace.{u1} G) (Lattice.toSemilatticeInf.{u1} (TopologicalSpace.{u1} G) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} G) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} G) (TopologicalSpace.completeLattice.{u1} G))))) t₁ t₂) _inst_1)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Inv.{u1} G] {t₁ : TopologicalSpace.{u1} G} {t₂ : TopologicalSpace.{u1} G}, (ContinuousInv.{u1} G t₁ _inst_1) -> (ContinuousInv.{u1} G t₂ _inst_1) -> (ContinuousInv.{u1} G (Inf.inf.{u1} (TopologicalSpace.{u1} G) (Lattice.toInf.{u1} (TopologicalSpace.{u1} G) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} G) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} G) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} G)))) t₁ t₂) _inst_1)
Case conversion may be inaccurate. Consider using '#align has_continuous_inv_inf continuousInv_infₓ'. -/
@[to_additive]
theorem continuousInv_inf {t₁ t₂ : TopologicalSpace G} (h₁ : @ContinuousInv G t₁ _)
    (h₂ : @ContinuousInv G t₂ _) : @ContinuousInv G (t₁ ⊓ t₂) _ :=
  by
  rw [inf_eq_infᵢ]
  refine' continuousInv_infᵢ fun b => _
  cases b <;> assumption
#align has_continuous_inv_inf continuousInv_inf
#align has_continuous_neg_inf continuousNeg_inf

end LatticeOps

/- warning: inducing.has_continuous_inv -> Inducing.continuousInv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : Inv.{u1} G] [_inst_2 : Inv.{u2} H] [_inst_3 : TopologicalSpace.{u1} G] [_inst_4 : TopologicalSpace.{u2} H] [_inst_5 : ContinuousInv.{u2} H _inst_4 _inst_2] {f : G -> H}, (Inducing.{u1, u2} G H _inst_3 _inst_4 f) -> (forall (x : G), Eq.{succ u2} H (f (Inv.inv.{u1} G _inst_1 x)) (Inv.inv.{u2} H _inst_2 (f x))) -> (ContinuousInv.{u1} G _inst_3 _inst_1)
but is expected to have type
  forall {G : Type.{u2}} {H : Type.{u1}} [_inst_1 : Inv.{u2} G] [_inst_2 : Inv.{u1} H] [_inst_3 : TopologicalSpace.{u2} G] [_inst_4 : TopologicalSpace.{u1} H] [_inst_5 : ContinuousInv.{u1} H _inst_4 _inst_2] {f : G -> H}, (Inducing.{u2, u1} G H _inst_3 _inst_4 f) -> (forall (x : G), Eq.{succ u1} H (f (Inv.inv.{u2} G _inst_1 x)) (Inv.inv.{u1} H _inst_2 (f x))) -> (ContinuousInv.{u2} G _inst_3 _inst_1)
Case conversion may be inaccurate. Consider using '#align inducing.has_continuous_inv Inducing.continuousInvₓ'. -/
@[to_additive]
theorem Inducing.continuousInv {G H : Type _} [Inv G] [Inv H] [TopologicalSpace G]
    [TopologicalSpace H] [ContinuousInv H] {f : G → H} (hf : Inducing f)
    (hf_inv : ∀ x, f x⁻¹ = (f x)⁻¹) : ContinuousInv G :=
  ⟨hf.continuous_iff.2 <| by simpa only [(· ∘ ·), hf_inv] using hf.continuous.inv⟩
#align inducing.has_continuous_inv Inducing.continuousInv
#align inducing.has_continuous_neg Inducing.continuousNeg

section TopologicalGroup

/-!
### Topological groups

A topological group is a group in which the multiplication and inversion operations are
continuous. Topological additive groups are defined in the same way. Equivalently, we can require
that the division operation `λ x y, x * y⁻¹` (resp., subtraction) is continuous.
-/


#print TopologicalAddGroup /-
/-- A topological (additive) group is a group in which the addition and negation operations are
continuous. -/
class TopologicalAddGroup (G : Type u) [TopologicalSpace G] [AddGroup G] extends ContinuousAdd G,
  ContinuousNeg G : Prop
#align topological_add_group TopologicalAddGroup
-/

#print TopologicalGroup /-
/-- A topological group is a group in which the multiplication and inversion operations are
continuous.

When you declare an instance that does not already have a `uniform_space` instance,
you should also provide an instance of `uniform_space` and `uniform_group` using
`topological_group.to_uniform_space` and `topological_comm_group_is_uniform`. -/
@[to_additive]
class TopologicalGroup (G : Type _) [TopologicalSpace G] [Group G] extends ContinuousMul G,
  ContinuousInv G : Prop
#align topological_group TopologicalGroup
#align topological_add_group TopologicalAddGroup
-/

section Conj

/- warning: conj_act.units_has_continuous_const_smul -> ConjAct.units_continuousConstSMul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))], ContinuousConstSMul.{u1, u1} (ConjAct.{u1} (Units.{u1} M _inst_1)) M _inst_2 (ConjAct.unitsScalar.{u1} M _inst_1)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))], ContinuousConstSMul.{u1, u1} (ConjAct.{u1} (Units.{u1} M _inst_1)) M _inst_2 (ConjAct.unitsScalar.{u1} M _inst_1)
Case conversion may be inaccurate. Consider using '#align conj_act.units_has_continuous_const_smul ConjAct.units_continuousConstSMulₓ'. -/
instance ConjAct.units_continuousConstSMul {M} [Monoid M] [TopologicalSpace M] [ContinuousMul M] :
    ContinuousConstSMul (ConjAct Mˣ) M :=
  ⟨fun m => (continuous_const.mul continuous_id).mul continuous_const⟩
#align conj_act.units_has_continuous_const_smul ConjAct.units_continuousConstSMul

variable [TopologicalSpace G] [Inv G] [Mul G] [ContinuousMul G]

/- warning: topological_group.continuous_conj_prod -> TopologicalGroup.continuous_conj_prod is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Inv.{u1} G] [_inst_3 : Mul.{u1} G] [_inst_4 : ContinuousMul.{u1} G _inst_1 _inst_3] [_inst_5 : ContinuousInv.{u1} G _inst_1 _inst_2], Continuous.{u1, u1} (Prod.{u1, u1} G G) G (Prod.topologicalSpace.{u1, u1} G G _inst_1 _inst_1) _inst_1 (fun (g : Prod.{u1, u1} G G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G _inst_3) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G _inst_3) (Prod.fst.{u1, u1} G G g) (Prod.snd.{u1, u1} G G g)) (Inv.inv.{u1} G _inst_2 (Prod.fst.{u1, u1} G G g)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Inv.{u1} G] [_inst_3 : Mul.{u1} G] [_inst_4 : ContinuousMul.{u1} G _inst_1 _inst_3] [_inst_5 : ContinuousInv.{u1} G _inst_1 _inst_2], Continuous.{u1, u1} (Prod.{u1, u1} G G) G (instTopologicalSpaceProd.{u1, u1} G G _inst_1 _inst_1) _inst_1 (fun (g : Prod.{u1, u1} G G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G _inst_3) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G _inst_3) (Prod.fst.{u1, u1} G G g) (Prod.snd.{u1, u1} G G g)) (Inv.inv.{u1} G _inst_2 (Prod.fst.{u1, u1} G G g)))
Case conversion may be inaccurate. Consider using '#align topological_group.continuous_conj_prod TopologicalGroup.continuous_conj_prodₓ'. -/
/-- Conjugation is jointly continuous on `G × G` when both `mul` and `inv` are continuous. -/
@[to_additive
      "Conjugation is jointly continuous on `G × G` when both `mul` and `inv` are\ncontinuous."]
theorem TopologicalGroup.continuous_conj_prod [ContinuousInv G] :
    Continuous fun g : G × G => g.fst * g.snd * g.fst⁻¹ :=
  continuous_mul.mul (continuous_inv.comp continuous_fst)
#align topological_group.continuous_conj_prod TopologicalGroup.continuous_conj_prod
#align topological_add_group.continuous_conj_sum TopologicalAddGroup.continuous_conj_sum

#print TopologicalGroup.continuous_conj /-
/-- Conjugation by a fixed element is continuous when `mul` is continuous. -/
@[to_additive "Conjugation by a fixed element is continuous when `add` is continuous."]
theorem TopologicalGroup.continuous_conj (g : G) : Continuous fun h : G => g * h * g⁻¹ :=
  (continuous_mul_right g⁻¹).comp (continuous_mul_left g)
#align topological_group.continuous_conj TopologicalGroup.continuous_conj
#align topological_add_group.continuous_conj TopologicalAddGroup.continuous_conj
-/

#print TopologicalGroup.continuous_conj' /-
/-- Conjugation acting on fixed element of the group is continuous when both `mul` and
`inv` are continuous. -/
@[to_additive
      "Conjugation acting on fixed element of the additive group is continuous when both\n  `add` and `neg` are continuous."]
theorem TopologicalGroup.continuous_conj' [ContinuousInv G] (h : G) :
    Continuous fun g : G => g * h * g⁻¹ :=
  (continuous_mul_right h).mul continuous_inv
#align topological_group.continuous_conj' TopologicalGroup.continuous_conj'
#align topological_add_group.continuous_conj' TopologicalAddGroup.continuous_conj'
-/

end Conj

variable [TopologicalSpace G] [Group G] [TopologicalGroup G] [TopologicalSpace α] {f : α → G}
  {s : Set α} {x : α}

section Zpow

#print continuous_zpow /-
@[continuity, to_additive]
theorem continuous_zpow : ∀ z : ℤ, Continuous fun a : G => a ^ z
  | Int.ofNat n => by simpa using continuous_pow n
  | -[n+1] => by simpa using (continuous_pow (n + 1)).inv
#align continuous_zpow continuous_zpow
#align continuous_zsmul continuous_zsmul
-/

#print AddGroup.continuousConstSMul_int /-
instance AddGroup.continuousConstSMul_int {A} [AddGroup A] [TopologicalSpace A]
    [TopologicalAddGroup A] : ContinuousConstSMul ℤ A :=
  ⟨continuous_zsmul⟩
#align add_group.has_continuous_const_smul_int AddGroup.continuousConstSMul_int
-/

/- warning: add_group.has_continuous_smul_int -> AddGroup.continuousSmul_int is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_5 : AddGroup.{u1} A] [_inst_6 : TopologicalSpace.{u1} A] [_inst_7 : TopologicalAddGroup.{u1} A _inst_6 _inst_5], ContinuousSMul.{0, u1} Int A (SubNegMonoid.SMulInt.{u1} A (AddGroup.toSubNegMonoid.{u1} A _inst_5)) Int.topologicalSpace _inst_6
but is expected to have type
  forall {A : Type.{u1}} [_inst_5 : AddGroup.{u1} A] [_inst_6 : TopologicalSpace.{u1} A] [_inst_7 : TopologicalAddGroup.{u1} A _inst_6 _inst_5], ContinuousSMul.{0, u1} Int A (SubNegMonoid.SMulInt.{u1} A (AddGroup.toSubNegMonoid.{u1} A _inst_5)) instTopologicalSpaceInt _inst_6
Case conversion may be inaccurate. Consider using '#align add_group.has_continuous_smul_int AddGroup.continuousSmul_intₓ'. -/
instance AddGroup.continuousSmul_int {A} [AddGroup A] [TopologicalSpace A] [TopologicalAddGroup A] :
    ContinuousSMul ℤ A :=
  ⟨continuous_uncurry_of_discreteTopology continuous_zsmul⟩
#align add_group.has_continuous_smul_int AddGroup.continuousSmul_int

#print Continuous.zpow /-
@[continuity, to_additive]
theorem Continuous.zpow {f : α → G} (h : Continuous f) (z : ℤ) : Continuous fun b => f b ^ z :=
  (continuous_zpow z).comp h
#align continuous.zpow Continuous.zpow
#align continuous.zsmul Continuous.zsmul
-/

#print continuousOn_zpow /-
@[to_additive]
theorem continuousOn_zpow {s : Set G} (z : ℤ) : ContinuousOn (fun x => x ^ z) s :=
  (continuous_zpow z).ContinuousOn
#align continuous_on_zpow continuousOn_zpow
#align continuous_on_zsmul continuousOn_zsmul
-/

#print continuousAt_zpow /-
@[to_additive]
theorem continuousAt_zpow (x : G) (z : ℤ) : ContinuousAt (fun x => x ^ z) x :=
  (continuous_zpow z).ContinuousAt
#align continuous_at_zpow continuousAt_zpow
#align continuous_at_zsmul continuousAt_zsmul
-/

/- warning: filter.tendsto.zpow -> Filter.Tendsto.zpow is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] {α : Type.{u2}} {l : Filter.{u2} α} {f : α -> G} {x : G}, (Filter.Tendsto.{u2, u1} α G f l (nhds.{u1} G _inst_1 x)) -> (forall (z : Int), Filter.Tendsto.{u2, u1} α G (fun (x : α) => HPow.hPow.{u1, 0, u1} G Int G (instHPow.{u1, 0} G Int (DivInvMonoid.Pow.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (f x) z) l (nhds.{u1} G _inst_1 (HPow.hPow.{u1, 0, u1} G Int G (instHPow.{u1, 0} G Int (DivInvMonoid.Pow.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) x z)))
but is expected to have type
  forall {G : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} G] [_inst_2 : Group.{u2} G] [_inst_3 : TopologicalGroup.{u2} G _inst_1 _inst_2] {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> G} {x : G}, (Filter.Tendsto.{u1, u2} α G f l (nhds.{u2} G _inst_1 x)) -> (forall (z : Int), Filter.Tendsto.{u1, u2} α G (fun (x : α) => HPow.hPow.{u2, 0, u2} G Int G (instHPow.{u2, 0} G Int (DivInvMonoid.Pow.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))) (f x) z) l (nhds.{u2} G _inst_1 (HPow.hPow.{u2, 0, u2} G Int G (instHPow.{u2, 0} G Int (DivInvMonoid.Pow.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))) x z)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.zpow Filter.Tendsto.zpowₓ'. -/
@[to_additive]
theorem Filter.Tendsto.zpow {α} {l : Filter α} {f : α → G} {x : G} (hf : Tendsto f l (𝓝 x))
    (z : ℤ) : Tendsto (fun x => f x ^ z) l (𝓝 (x ^ z)) :=
  (continuousAt_zpow _ _).Tendsto.comp hf
#align filter.tendsto.zpow Filter.Tendsto.zpow
#align filter.tendsto.zsmul Filter.Tendsto.zsmul

#print ContinuousWithinAt.zpow /-
@[to_additive]
theorem ContinuousWithinAt.zpow {f : α → G} {x : α} {s : Set α} (hf : ContinuousWithinAt f s x)
    (z : ℤ) : ContinuousWithinAt (fun x => f x ^ z) s x :=
  hf.zpow z
#align continuous_within_at.zpow ContinuousWithinAt.zpow
#align continuous_within_at.zsmul ContinuousWithinAt.zsmul
-/

#print ContinuousAt.zpow /-
@[to_additive]
theorem ContinuousAt.zpow {f : α → G} {x : α} (hf : ContinuousAt f x) (z : ℤ) :
    ContinuousAt (fun x => f x ^ z) x :=
  hf.zpow z
#align continuous_at.zpow ContinuousAt.zpow
#align continuous_at.zsmul ContinuousAt.zsmul
-/

#print ContinuousOn.zpow /-
@[to_additive ContinuousOn.zsmul]
theorem ContinuousOn.zpow {f : α → G} {s : Set α} (hf : ContinuousOn f s) (z : ℤ) :
    ContinuousOn (fun x => f x ^ z) s := fun x hx => (hf x hx).zpow z
#align continuous_on.zpow ContinuousOn.zpow
#align continuous_on.zsmul ContinuousOn.zsmul
-/

end Zpow

section OrderedCommGroup

variable [TopologicalSpace H] [OrderedCommGroup H] [ContinuousInv H]

/- warning: tendsto_inv_nhds_within_Ioi -> tendsto_inv_nhdsWithin_Ioi is a dubious translation:
lean 3 declaration is
  forall {H : Type.{u1}} [_inst_5 : TopologicalSpace.{u1} H] [_inst_6 : OrderedCommGroup.{u1} H] [_inst_7 : ContinuousInv.{u1} H _inst_5 (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))] {a : H}, Filter.Tendsto.{u1, u1} H H (Inv.inv.{u1} H (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))) (nhdsWithin.{u1} H _inst_5 a (Set.Ioi.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) a)) (nhdsWithin.{u1} H _inst_5 (Inv.inv.{u1} H (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))) a) (Set.Iio.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) (Inv.inv.{u1} H (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))) a)))
but is expected to have type
  forall {H : Type.{u1}} [_inst_5 : TopologicalSpace.{u1} H] [_inst_6 : OrderedCommGroup.{u1} H] [_inst_7 : ContinuousInv.{u1} H _inst_5 (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))))] {a : H}, Filter.Tendsto.{u1, u1} H H (Inv.inv.{u1} H (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))))) (nhdsWithin.{u1} H _inst_5 a (Set.Ioi.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) a)) (nhdsWithin.{u1} H _inst_5 (Inv.inv.{u1} H (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))))) a) (Set.Iio.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) (Inv.inv.{u1} H (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))))) a)))
Case conversion may be inaccurate. Consider using '#align tendsto_inv_nhds_within_Ioi tendsto_inv_nhdsWithin_Ioiₓ'. -/
@[to_additive]
theorem tendsto_inv_nhdsWithin_Ioi {a : H} : Tendsto Inv.inv (𝓝[>] a) (𝓝[<] a⁻¹) :=
  (continuous_inv.Tendsto a).inf <| by simp [tendsto_principal_principal]
#align tendsto_inv_nhds_within_Ioi tendsto_inv_nhdsWithin_Ioi
#align tendsto_neg_nhds_within_Ioi tendsto_neg_nhdsWithin_Ioi

/- warning: tendsto_inv_nhds_within_Iio -> tendsto_inv_nhdsWithin_Iio is a dubious translation:
lean 3 declaration is
  forall {H : Type.{u1}} [_inst_5 : TopologicalSpace.{u1} H] [_inst_6 : OrderedCommGroup.{u1} H] [_inst_7 : ContinuousInv.{u1} H _inst_5 (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))] {a : H}, Filter.Tendsto.{u1, u1} H H (Inv.inv.{u1} H (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))) (nhdsWithin.{u1} H _inst_5 a (Set.Iio.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) a)) (nhdsWithin.{u1} H _inst_5 (Inv.inv.{u1} H (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))) a) (Set.Ioi.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) (Inv.inv.{u1} H (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))) a)))
but is expected to have type
  forall {H : Type.{u1}} [_inst_5 : TopologicalSpace.{u1} H] [_inst_6 : OrderedCommGroup.{u1} H] [_inst_7 : ContinuousInv.{u1} H _inst_5 (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))))] {a : H}, Filter.Tendsto.{u1, u1} H H (Inv.inv.{u1} H (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))))) (nhdsWithin.{u1} H _inst_5 a (Set.Iio.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) a)) (nhdsWithin.{u1} H _inst_5 (Inv.inv.{u1} H (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))))) a) (Set.Ioi.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) (Inv.inv.{u1} H (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))))) a)))
Case conversion may be inaccurate. Consider using '#align tendsto_inv_nhds_within_Iio tendsto_inv_nhdsWithin_Iioₓ'. -/
@[to_additive]
theorem tendsto_inv_nhdsWithin_Iio {a : H} : Tendsto Inv.inv (𝓝[<] a) (𝓝[>] a⁻¹) :=
  (continuous_inv.Tendsto a).inf <| by simp [tendsto_principal_principal]
#align tendsto_inv_nhds_within_Iio tendsto_inv_nhdsWithin_Iio
#align tendsto_neg_nhds_within_Iio tendsto_neg_nhdsWithin_Iio

/- warning: tendsto_inv_nhds_within_Ioi_inv -> tendsto_inv_nhdsWithin_Ioi_inv is a dubious translation:
lean 3 declaration is
  forall {H : Type.{u1}} [_inst_5 : TopologicalSpace.{u1} H] [_inst_6 : OrderedCommGroup.{u1} H] [_inst_7 : ContinuousInv.{u1} H _inst_5 (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))] {a : H}, Filter.Tendsto.{u1, u1} H H (Inv.inv.{u1} H (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))) (nhdsWithin.{u1} H _inst_5 (Inv.inv.{u1} H (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))) a) (Set.Ioi.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) (Inv.inv.{u1} H (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))) a))) (nhdsWithin.{u1} H _inst_5 a (Set.Iio.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) a))
but is expected to have type
  forall {H : Type.{u1}} [_inst_5 : TopologicalSpace.{u1} H] [_inst_6 : OrderedCommGroup.{u1} H] [_inst_7 : ContinuousInv.{u1} H _inst_5 (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))))] {a : H}, Filter.Tendsto.{u1, u1} H H (Inv.inv.{u1} H (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))))) (nhdsWithin.{u1} H _inst_5 (Inv.inv.{u1} H (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))))) a) (Set.Ioi.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) (Inv.inv.{u1} H (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))))) a))) (nhdsWithin.{u1} H _inst_5 a (Set.Iio.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) a))
Case conversion may be inaccurate. Consider using '#align tendsto_inv_nhds_within_Ioi_inv tendsto_inv_nhdsWithin_Ioi_invₓ'. -/
@[to_additive]
theorem tendsto_inv_nhdsWithin_Ioi_inv {a : H} : Tendsto Inv.inv (𝓝[>] a⁻¹) (𝓝[<] a) := by
  simpa only [inv_inv] using @tendsto_inv_nhdsWithin_Ioi _ _ _ _ a⁻¹
#align tendsto_inv_nhds_within_Ioi_inv tendsto_inv_nhdsWithin_Ioi_inv
#align tendsto_neg_nhds_within_Ioi_neg tendsto_neg_nhdsWithin_Ioi_neg

/- warning: tendsto_inv_nhds_within_Iio_inv -> tendsto_inv_nhdsWithin_Iio_inv is a dubious translation:
lean 3 declaration is
  forall {H : Type.{u1}} [_inst_5 : TopologicalSpace.{u1} H] [_inst_6 : OrderedCommGroup.{u1} H] [_inst_7 : ContinuousInv.{u1} H _inst_5 (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))] {a : H}, Filter.Tendsto.{u1, u1} H H (Inv.inv.{u1} H (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))) (nhdsWithin.{u1} H _inst_5 (Inv.inv.{u1} H (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))) a) (Set.Iio.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) (Inv.inv.{u1} H (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))) a))) (nhdsWithin.{u1} H _inst_5 a (Set.Ioi.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) a))
but is expected to have type
  forall {H : Type.{u1}} [_inst_5 : TopologicalSpace.{u1} H] [_inst_6 : OrderedCommGroup.{u1} H] [_inst_7 : ContinuousInv.{u1} H _inst_5 (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))))] {a : H}, Filter.Tendsto.{u1, u1} H H (Inv.inv.{u1} H (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))))) (nhdsWithin.{u1} H _inst_5 (Inv.inv.{u1} H (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))))) a) (Set.Iio.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) (Inv.inv.{u1} H (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))))) a))) (nhdsWithin.{u1} H _inst_5 a (Set.Ioi.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) a))
Case conversion may be inaccurate. Consider using '#align tendsto_inv_nhds_within_Iio_inv tendsto_inv_nhdsWithin_Iio_invₓ'. -/
@[to_additive]
theorem tendsto_inv_nhdsWithin_Iio_inv {a : H} : Tendsto Inv.inv (𝓝[<] a⁻¹) (𝓝[>] a) := by
  simpa only [inv_inv] using @tendsto_inv_nhdsWithin_Iio _ _ _ _ a⁻¹
#align tendsto_inv_nhds_within_Iio_inv tendsto_inv_nhdsWithin_Iio_inv
#align tendsto_neg_nhds_within_Iio_neg tendsto_neg_nhdsWithin_Iio_neg

/- warning: tendsto_inv_nhds_within_Ici -> tendsto_inv_nhdsWithin_Ici is a dubious translation:
lean 3 declaration is
  forall {H : Type.{u1}} [_inst_5 : TopologicalSpace.{u1} H] [_inst_6 : OrderedCommGroup.{u1} H] [_inst_7 : ContinuousInv.{u1} H _inst_5 (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))] {a : H}, Filter.Tendsto.{u1, u1} H H (Inv.inv.{u1} H (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))) (nhdsWithin.{u1} H _inst_5 a (Set.Ici.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) a)) (nhdsWithin.{u1} H _inst_5 (Inv.inv.{u1} H (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))) a) (Set.Iic.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) (Inv.inv.{u1} H (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))) a)))
but is expected to have type
  forall {H : Type.{u1}} [_inst_5 : TopologicalSpace.{u1} H] [_inst_6 : OrderedCommGroup.{u1} H] [_inst_7 : ContinuousInv.{u1} H _inst_5 (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))))] {a : H}, Filter.Tendsto.{u1, u1} H H (Inv.inv.{u1} H (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))))) (nhdsWithin.{u1} H _inst_5 a (Set.Ici.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) a)) (nhdsWithin.{u1} H _inst_5 (Inv.inv.{u1} H (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))))) a) (Set.Iic.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) (Inv.inv.{u1} H (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))))) a)))
Case conversion may be inaccurate. Consider using '#align tendsto_inv_nhds_within_Ici tendsto_inv_nhdsWithin_Iciₓ'. -/
@[to_additive]
theorem tendsto_inv_nhdsWithin_Ici {a : H} : Tendsto Inv.inv (𝓝[≥] a) (𝓝[≤] a⁻¹) :=
  (continuous_inv.Tendsto a).inf <| by simp [tendsto_principal_principal]
#align tendsto_inv_nhds_within_Ici tendsto_inv_nhdsWithin_Ici
#align tendsto_neg_nhds_within_Ici tendsto_neg_nhdsWithin_Ici

/- warning: tendsto_inv_nhds_within_Iic -> tendsto_inv_nhdsWithin_Iic is a dubious translation:
lean 3 declaration is
  forall {H : Type.{u1}} [_inst_5 : TopologicalSpace.{u1} H] [_inst_6 : OrderedCommGroup.{u1} H] [_inst_7 : ContinuousInv.{u1} H _inst_5 (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))] {a : H}, Filter.Tendsto.{u1, u1} H H (Inv.inv.{u1} H (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))) (nhdsWithin.{u1} H _inst_5 a (Set.Iic.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) a)) (nhdsWithin.{u1} H _inst_5 (Inv.inv.{u1} H (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))) a) (Set.Ici.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) (Inv.inv.{u1} H (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))) a)))
but is expected to have type
  forall {H : Type.{u1}} [_inst_5 : TopologicalSpace.{u1} H] [_inst_6 : OrderedCommGroup.{u1} H] [_inst_7 : ContinuousInv.{u1} H _inst_5 (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))))] {a : H}, Filter.Tendsto.{u1, u1} H H (Inv.inv.{u1} H (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))))) (nhdsWithin.{u1} H _inst_5 a (Set.Iic.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) a)) (nhdsWithin.{u1} H _inst_5 (Inv.inv.{u1} H (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))))) a) (Set.Ici.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) (Inv.inv.{u1} H (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))))) a)))
Case conversion may be inaccurate. Consider using '#align tendsto_inv_nhds_within_Iic tendsto_inv_nhdsWithin_Iicₓ'. -/
@[to_additive]
theorem tendsto_inv_nhdsWithin_Iic {a : H} : Tendsto Inv.inv (𝓝[≤] a) (𝓝[≥] a⁻¹) :=
  (continuous_inv.Tendsto a).inf <| by simp [tendsto_principal_principal]
#align tendsto_inv_nhds_within_Iic tendsto_inv_nhdsWithin_Iic
#align tendsto_neg_nhds_within_Iic tendsto_neg_nhdsWithin_Iic

/- warning: tendsto_inv_nhds_within_Ici_inv -> tendsto_inv_nhdsWithin_Ici_inv is a dubious translation:
lean 3 declaration is
  forall {H : Type.{u1}} [_inst_5 : TopologicalSpace.{u1} H] [_inst_6 : OrderedCommGroup.{u1} H] [_inst_7 : ContinuousInv.{u1} H _inst_5 (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))] {a : H}, Filter.Tendsto.{u1, u1} H H (Inv.inv.{u1} H (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))) (nhdsWithin.{u1} H _inst_5 (Inv.inv.{u1} H (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))) a) (Set.Ici.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) (Inv.inv.{u1} H (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))) a))) (nhdsWithin.{u1} H _inst_5 a (Set.Iic.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) a))
but is expected to have type
  forall {H : Type.{u1}} [_inst_5 : TopologicalSpace.{u1} H] [_inst_6 : OrderedCommGroup.{u1} H] [_inst_7 : ContinuousInv.{u1} H _inst_5 (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))))] {a : H}, Filter.Tendsto.{u1, u1} H H (Inv.inv.{u1} H (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))))) (nhdsWithin.{u1} H _inst_5 (Inv.inv.{u1} H (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))))) a) (Set.Ici.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) (Inv.inv.{u1} H (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))))) a))) (nhdsWithin.{u1} H _inst_5 a (Set.Iic.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) a))
Case conversion may be inaccurate. Consider using '#align tendsto_inv_nhds_within_Ici_inv tendsto_inv_nhdsWithin_Ici_invₓ'. -/
@[to_additive]
theorem tendsto_inv_nhdsWithin_Ici_inv {a : H} : Tendsto Inv.inv (𝓝[≥] a⁻¹) (𝓝[≤] a) := by
  simpa only [inv_inv] using @tendsto_inv_nhdsWithin_Ici _ _ _ _ a⁻¹
#align tendsto_inv_nhds_within_Ici_inv tendsto_inv_nhdsWithin_Ici_inv
#align tendsto_neg_nhds_within_Ici_neg tendsto_neg_nhdsWithin_Ici_neg

/- warning: tendsto_inv_nhds_within_Iic_inv -> tendsto_inv_nhdsWithin_Iic_inv is a dubious translation:
lean 3 declaration is
  forall {H : Type.{u1}} [_inst_5 : TopologicalSpace.{u1} H] [_inst_6 : OrderedCommGroup.{u1} H] [_inst_7 : ContinuousInv.{u1} H _inst_5 (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))] {a : H}, Filter.Tendsto.{u1, u1} H H (Inv.inv.{u1} H (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))) (nhdsWithin.{u1} H _inst_5 (Inv.inv.{u1} H (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))) a) (Set.Iic.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) (Inv.inv.{u1} H (DivInvMonoid.toHasInv.{u1} H (Group.toDivInvMonoid.{u1} H (CommGroup.toGroup.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))) a))) (nhdsWithin.{u1} H _inst_5 a (Set.Ici.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) a))
but is expected to have type
  forall {H : Type.{u1}} [_inst_5 : TopologicalSpace.{u1} H] [_inst_6 : OrderedCommGroup.{u1} H] [_inst_7 : ContinuousInv.{u1} H _inst_5 (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))))] {a : H}, Filter.Tendsto.{u1, u1} H H (Inv.inv.{u1} H (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6))))))) (nhdsWithin.{u1} H _inst_5 (Inv.inv.{u1} H (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))))) a) (Set.Iic.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) (Inv.inv.{u1} H (InvOneClass.toInv.{u1} H (DivInvOneMonoid.toInvOneClass.{u1} H (DivisionMonoid.toDivInvOneMonoid.{u1} H (DivisionCommMonoid.toDivisionMonoid.{u1} H (CommGroup.toDivisionCommMonoid.{u1} H (OrderedCommGroup.toCommGroup.{u1} H _inst_6)))))) a))) (nhdsWithin.{u1} H _inst_5 a (Set.Ici.{u1} H (PartialOrder.toPreorder.{u1} H (OrderedCommGroup.toPartialOrder.{u1} H _inst_6)) a))
Case conversion may be inaccurate. Consider using '#align tendsto_inv_nhds_within_Iic_inv tendsto_inv_nhdsWithin_Iic_invₓ'. -/
@[to_additive]
theorem tendsto_inv_nhdsWithin_Iic_inv {a : H} : Tendsto Inv.inv (𝓝[≤] a⁻¹) (𝓝[≥] a) := by
  simpa only [inv_inv] using @tendsto_inv_nhdsWithin_Iic _ _ _ _ a⁻¹
#align tendsto_inv_nhds_within_Iic_inv tendsto_inv_nhdsWithin_Iic_inv
#align tendsto_neg_nhds_within_Iic_neg tendsto_neg_nhdsWithin_Iic_neg

end OrderedCommGroup

@[instance, to_additive]
instance [TopologicalSpace H] [Group H] [TopologicalGroup H] : TopologicalGroup (G × H)
    where continuous_inv := continuous_inv.Prod_map continuous_inv

#print Pi.topologicalGroup /-
@[to_additive]
instance Pi.topologicalGroup {C : β → Type _} [∀ b, TopologicalSpace (C b)] [∀ b, Group (C b)]
    [∀ b, TopologicalGroup (C b)] : TopologicalGroup (∀ b, C b)
    where continuous_inv := continuous_pi fun i => (continuous_apply i).inv
#align pi.topological_group Pi.topologicalGroup
#align pi.topological_add_group Pi.topologicalAddGroup
-/

open MulOpposite

@[to_additive]
instance [Inv α] [ContinuousInv α] : ContinuousInv αᵐᵒᵖ :=
  opHomeomorph.symm.Inducing.ContinuousInv unop_inv

/-- If multiplication is continuous in `α`, then it also is in `αᵐᵒᵖ`. -/
@[to_additive "If addition is continuous in `α`, then it also is in `αᵃᵒᵖ`."]
instance [Group α] [TopologicalGroup α] : TopologicalGroup αᵐᵒᵖ where

variable (G)

/- warning: nhds_one_symm -> nhds_one_symm is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2], Eq.{succ u1} (Filter.{u1} G) (Filter.comap.{u1, u1} G G (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))))))) (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))))))
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2], Eq.{succ u1} (Filter.{u1} G) (Filter.comap.{u1, u1} G G (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2))))) (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))))))) (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))))))
Case conversion may be inaccurate. Consider using '#align nhds_one_symm nhds_one_symmₓ'. -/
@[to_additive]
theorem nhds_one_symm : comap Inv.inv (𝓝 (1 : G)) = 𝓝 (1 : G) :=
  ((Homeomorph.inv G).comap_nhds_eq _).trans (congr_arg nhds inv_one)
#align nhds_one_symm nhds_one_symm
#align nhds_zero_symm nhds_zero_symm

/- warning: nhds_one_symm' -> nhds_one_symm' is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2], Eq.{succ u1} (Filter.{u1} G) (Filter.map.{u1, u1} G G (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))))))) (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))))))
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2], Eq.{succ u1} (Filter.{u1} G) (Filter.map.{u1, u1} G G (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2))))) (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))))))) (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))))))
Case conversion may be inaccurate. Consider using '#align nhds_one_symm' nhds_one_symm'ₓ'. -/
@[to_additive]
theorem nhds_one_symm' : map Inv.inv (𝓝 (1 : G)) = 𝓝 (1 : G) :=
  ((Homeomorph.inv G).map_nhds_eq _).trans (congr_arg nhds inv_one)
#align nhds_one_symm' nhds_one_symm'
#align nhds_zero_symm' nhds_zero_symm'

/- warning: inv_mem_nhds_one -> inv_mem_nhds_one is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] {S : Set.{u1} G}, (Membership.Mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (Filter.hasMem.{u1} G) S (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))))))) -> (Membership.Mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (Filter.hasMem.{u1} G) (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) S) (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))))))
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] {S : Set.{u1} G}, (Membership.mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (instMembershipSetFilter.{u1} G) S (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))))))) -> (Membership.mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (instMembershipSetFilter.{u1} G) (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2))))) S) (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align inv_mem_nhds_one inv_mem_nhds_oneₓ'. -/
@[to_additive]
theorem inv_mem_nhds_one {S : Set G} (hS : S ∈ (𝓝 1 : Filter G)) : S⁻¹ ∈ 𝓝 (1 : G) := by
  rwa [← nhds_one_symm'] at hS
#align inv_mem_nhds_one inv_mem_nhds_one
#align neg_mem_nhds_zero neg_mem_nhds_zero

/- warning: homeomorph.shear_mul_right -> Homeomorph.shearMulRight is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2], Homeomorph.{u1, u1} (Prod.{u1, u1} G G) (Prod.{u1, u1} G G) (Prod.topologicalSpace.{u1, u1} G G _inst_1 _inst_1) (Prod.topologicalSpace.{u1, u1} G G _inst_1 _inst_1)
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2], Homeomorph.{u1, u1} (Prod.{u1, u1} G G) (Prod.{u1, u1} G G) (instTopologicalSpaceProd.{u1, u1} G G _inst_1 _inst_1) (instTopologicalSpaceProd.{u1, u1} G G _inst_1 _inst_1)
Case conversion may be inaccurate. Consider using '#align homeomorph.shear_mul_right Homeomorph.shearMulRightₓ'. -/
/-- The map `(x, y) ↦ (x, xy)` as a homeomorphism. This is a shear mapping. -/
@[to_additive "The map `(x, y) ↦ (x, x + y)` as a homeomorphism.\nThis is a shear mapping."]
protected def Homeomorph.shearMulRight : G × G ≃ₜ G × G :=
  {
    Equiv.prodShear (Equiv.refl _)
      Equiv.mulLeft with
    continuous_toFun := continuous_fst.prod_mk continuous_mul
    continuous_invFun := continuous_fst.prod_mk <| continuous_fst.inv.mul continuous_snd }
#align homeomorph.shear_mul_right Homeomorph.shearMulRight
#align homeomorph.shear_add_right Homeomorph.shearAddRight

/- warning: homeomorph.shear_mul_right_coe -> Homeomorph.shearMulRight_coe is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2], Eq.{succ u1} ((Prod.{u1, u1} G G) -> (Prod.{u1, u1} G G)) (coeFn.{succ u1, succ u1} (Homeomorph.{u1, u1} (Prod.{u1, u1} G G) (Prod.{u1, u1} G G) (Prod.topologicalSpace.{u1, u1} G G _inst_1 _inst_1) (Prod.topologicalSpace.{u1, u1} G G _inst_1 _inst_1)) (fun (_x : Homeomorph.{u1, u1} (Prod.{u1, u1} G G) (Prod.{u1, u1} G G) (Prod.topologicalSpace.{u1, u1} G G _inst_1 _inst_1) (Prod.topologicalSpace.{u1, u1} G G _inst_1 _inst_1)) => (Prod.{u1, u1} G G) -> (Prod.{u1, u1} G G)) (Homeomorph.hasCoeToFun.{u1, u1} (Prod.{u1, u1} G G) (Prod.{u1, u1} G G) (Prod.topologicalSpace.{u1, u1} G G _inst_1 _inst_1) (Prod.topologicalSpace.{u1, u1} G G _inst_1 _inst_1)) (Homeomorph.shearMulRight.{u1} G _inst_1 _inst_2 _inst_3)) (fun (z : Prod.{u1, u1} G G) => Prod.mk.{u1, u1} G G (Prod.fst.{u1, u1} G G z) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) (Prod.fst.{u1, u1} G G z) (Prod.snd.{u1, u1} G G z)))
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2], Eq.{succ u1} ((Prod.{u1, u1} G G) -> (Prod.{u1, u1} G G)) (FunLike.coe.{succ u1, succ u1, succ u1} (Homeomorph.{u1, u1} (Prod.{u1, u1} G G) (Prod.{u1, u1} G G) (instTopologicalSpaceProd.{u1, u1} G G _inst_1 _inst_1) (instTopologicalSpaceProd.{u1, u1} G G _inst_1 _inst_1)) (Prod.{u1, u1} G G) (fun (_x : Prod.{u1, u1} G G) => Prod.{u1, u1} G G) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Homeomorph.{u1, u1} (Prod.{u1, u1} G G) (Prod.{u1, u1} G G) (instTopologicalSpaceProd.{u1, u1} G G _inst_1 _inst_1) (instTopologicalSpaceProd.{u1, u1} G G _inst_1 _inst_1)) (Prod.{u1, u1} G G) (Prod.{u1, u1} G G) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Homeomorph.{u1, u1} (Prod.{u1, u1} G G) (Prod.{u1, u1} G G) (instTopologicalSpaceProd.{u1, u1} G G _inst_1 _inst_1) (instTopologicalSpaceProd.{u1, u1} G G _inst_1 _inst_1)) (Prod.{u1, u1} G G) (Prod.{u1, u1} G G) (Homeomorph.instEquivLikeHomeomorph.{u1, u1} (Prod.{u1, u1} G G) (Prod.{u1, u1} G G) (instTopologicalSpaceProd.{u1, u1} G G _inst_1 _inst_1) (instTopologicalSpaceProd.{u1, u1} G G _inst_1 _inst_1)))) (Homeomorph.shearMulRight.{u1} G _inst_1 _inst_2 _inst_3)) (fun (z : Prod.{u1, u1} G G) => Prod.mk.{u1, u1} G G (Prod.fst.{u1, u1} G G z) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) (Prod.fst.{u1, u1} G G z) (Prod.snd.{u1, u1} G G z)))
Case conversion may be inaccurate. Consider using '#align homeomorph.shear_mul_right_coe Homeomorph.shearMulRight_coeₓ'. -/
@[simp, to_additive]
theorem Homeomorph.shearMulRight_coe :
    ⇑(Homeomorph.shearMulRight G) = fun z : G × G => (z.1, z.1 * z.2) :=
  rfl
#align homeomorph.shear_mul_right_coe Homeomorph.shearMulRight_coe
#align homeomorph.shear_add_right_coe Homeomorph.shearAddRight_coe

/- warning: homeomorph.shear_mul_right_symm_coe -> Homeomorph.shearMulRight_symm_coe is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2], Eq.{succ u1} ((Prod.{u1, u1} G G) -> (Prod.{u1, u1} G G)) (coeFn.{succ u1, succ u1} (Homeomorph.{u1, u1} (Prod.{u1, u1} G G) (Prod.{u1, u1} G G) (Prod.topologicalSpace.{u1, u1} G G _inst_1 _inst_1) (Prod.topologicalSpace.{u1, u1} G G _inst_1 _inst_1)) (fun (_x : Homeomorph.{u1, u1} (Prod.{u1, u1} G G) (Prod.{u1, u1} G G) (Prod.topologicalSpace.{u1, u1} G G _inst_1 _inst_1) (Prod.topologicalSpace.{u1, u1} G G _inst_1 _inst_1)) => (Prod.{u1, u1} G G) -> (Prod.{u1, u1} G G)) (Homeomorph.hasCoeToFun.{u1, u1} (Prod.{u1, u1} G G) (Prod.{u1, u1} G G) (Prod.topologicalSpace.{u1, u1} G G _inst_1 _inst_1) (Prod.topologicalSpace.{u1, u1} G G _inst_1 _inst_1)) (Homeomorph.symm.{u1, u1} (Prod.{u1, u1} G G) (Prod.{u1, u1} G G) (Prod.topologicalSpace.{u1, u1} G G _inst_1 _inst_1) (Prod.topologicalSpace.{u1, u1} G G _inst_1 _inst_1) (Homeomorph.shearMulRight.{u1} G _inst_1 _inst_2 _inst_3))) (fun (z : Prod.{u1, u1} G G) => Prod.mk.{u1, u1} G G (Prod.fst.{u1, u1} G G z) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) (Prod.fst.{u1, u1} G G z)) (Prod.snd.{u1, u1} G G z)))
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2], Eq.{succ u1} ((Prod.{u1, u1} G G) -> (Prod.{u1, u1} G G)) (FunLike.coe.{succ u1, succ u1, succ u1} (Homeomorph.{u1, u1} (Prod.{u1, u1} G G) (Prod.{u1, u1} G G) (instTopologicalSpaceProd.{u1, u1} G G _inst_1 _inst_1) (instTopologicalSpaceProd.{u1, u1} G G _inst_1 _inst_1)) (Prod.{u1, u1} G G) (fun (_x : Prod.{u1, u1} G G) => Prod.{u1, u1} G G) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Homeomorph.{u1, u1} (Prod.{u1, u1} G G) (Prod.{u1, u1} G G) (instTopologicalSpaceProd.{u1, u1} G G _inst_1 _inst_1) (instTopologicalSpaceProd.{u1, u1} G G _inst_1 _inst_1)) (Prod.{u1, u1} G G) (Prod.{u1, u1} G G) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Homeomorph.{u1, u1} (Prod.{u1, u1} G G) (Prod.{u1, u1} G G) (instTopologicalSpaceProd.{u1, u1} G G _inst_1 _inst_1) (instTopologicalSpaceProd.{u1, u1} G G _inst_1 _inst_1)) (Prod.{u1, u1} G G) (Prod.{u1, u1} G G) (Homeomorph.instEquivLikeHomeomorph.{u1, u1} (Prod.{u1, u1} G G) (Prod.{u1, u1} G G) (instTopologicalSpaceProd.{u1, u1} G G _inst_1 _inst_1) (instTopologicalSpaceProd.{u1, u1} G G _inst_1 _inst_1)))) (Homeomorph.symm.{u1, u1} (Prod.{u1, u1} G G) (Prod.{u1, u1} G G) (instTopologicalSpaceProd.{u1, u1} G G _inst_1 _inst_1) (instTopologicalSpaceProd.{u1, u1} G G _inst_1 _inst_1) (Homeomorph.shearMulRight.{u1} G _inst_1 _inst_2 _inst_3))) (fun (z : Prod.{u1, u1} G G) => Prod.mk.{u1, u1} G G (Prod.fst.{u1, u1} G G z) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))) (Prod.fst.{u1, u1} G G z)) (Prod.snd.{u1, u1} G G z)))
Case conversion may be inaccurate. Consider using '#align homeomorph.shear_mul_right_symm_coe Homeomorph.shearMulRight_symm_coeₓ'. -/
@[simp, to_additive]
theorem Homeomorph.shearMulRight_symm_coe :
    ⇑(Homeomorph.shearMulRight G).symm = fun z : G × G => (z.1, z.1⁻¹ * z.2) :=
  rfl
#align homeomorph.shear_mul_right_symm_coe Homeomorph.shearMulRight_symm_coe
#align homeomorph.shear_add_right_symm_coe Homeomorph.shearAddRight_symm_coe

variable {G}

/- warning: inducing.topological_group -> Inducing.topologicalGroup is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] {F : Type.{u3}} [_inst_5 : Group.{u2} H] [_inst_6 : TopologicalSpace.{u2} H] [_inst_7 : MonoidHomClass.{u3, u2, u1} F H G (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_5))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))] (f : F), (Inducing.{u2, u1} H G _inst_6 _inst_1 (coeFn.{succ u3, max (succ u2) (succ u1)} F (fun (_x : F) => H -> G) (FunLike.hasCoeToFun.{succ u3, succ u2, succ u1} F H (fun (_x : H) => G) (MulHomClass.toFunLike.{u3, u2, u1} F H G (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_5)))) (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) (MonoidHomClass.toMulHomClass.{u3, u2, u1} F H G (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_5))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) _inst_7))) f)) -> (TopologicalGroup.{u2} H _inst_6 _inst_5)
but is expected to have type
  forall {G : Type.{u2}} {H : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} G] [_inst_2 : Group.{u2} G] [_inst_3 : TopologicalGroup.{u2} G _inst_1 _inst_2] {F : Type.{u1}} [_inst_5 : Group.{u3} H] [_inst_6 : TopologicalSpace.{u3} H] [_inst_7 : MonoidHomClass.{u1, u3, u2} F H G (Monoid.toMulOneClass.{u3} H (DivInvMonoid.toMonoid.{u3} H (Group.toDivInvMonoid.{u3} H _inst_5))) (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)))] (f : F), (Inducing.{u3, u2} H G _inst_6 _inst_1 (FunLike.coe.{succ u1, succ u3, succ u2} F H (fun (_x : H) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : H) => G) _x) (MulHomClass.toFunLike.{u1, u3, u2} F H G (MulOneClass.toMul.{u3} H (Monoid.toMulOneClass.{u3} H (DivInvMonoid.toMonoid.{u3} H (Group.toDivInvMonoid.{u3} H _inst_5)))) (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F H G (Monoid.toMulOneClass.{u3} H (DivInvMonoid.toMonoid.{u3} H (Group.toDivInvMonoid.{u3} H _inst_5))) (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))) _inst_7)) f)) -> (TopologicalGroup.{u3} H _inst_6 _inst_5)
Case conversion may be inaccurate. Consider using '#align inducing.topological_group Inducing.topologicalGroupₓ'. -/
@[to_additive]
protected theorem Inducing.topologicalGroup {F : Type _} [Group H] [TopologicalSpace H]
    [MonoidHomClass F H G] (f : F) (hf : Inducing f) : TopologicalGroup H :=
  { to_continuousMul := hf.ContinuousMul _
    to_continuousInv := hf.ContinuousInv (map_inv f) }
#align inducing.topological_group Inducing.topologicalGroup
#align inducing.topological_add_group Inducing.topologicalAddGroup

/- warning: topological_group_induced -> topologicalGroup_induced is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] {F : Type.{u3}} [_inst_5 : Group.{u2} H] [_inst_6 : MonoidHomClass.{u3, u2, u1} F H G (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_5))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))] (f : F), TopologicalGroup.{u2} H (TopologicalSpace.induced.{u2, u1} H G (coeFn.{succ u3, max (succ u2) (succ u1)} F (fun (_x : F) => H -> G) (FunLike.hasCoeToFun.{succ u3, succ u2, succ u1} F H (fun (_x : H) => G) (MulHomClass.toFunLike.{u3, u2, u1} F H G (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_5)))) (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) (MonoidHomClass.toMulHomClass.{u3, u2, u1} F H G (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_5))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) _inst_6))) f) _inst_1) _inst_5
but is expected to have type
  forall {G : Type.{u2}} {H : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} G] [_inst_2 : Group.{u2} G] [_inst_3 : TopologicalGroup.{u2} G _inst_1 _inst_2] {F : Type.{u1}} [_inst_5 : Group.{u3} H] [_inst_6 : MonoidHomClass.{u1, u3, u2} F H G (Monoid.toMulOneClass.{u3} H (DivInvMonoid.toMonoid.{u3} H (Group.toDivInvMonoid.{u3} H _inst_5))) (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)))] (f : F), TopologicalGroup.{u3} H (TopologicalSpace.induced.{u3, u2} H G (FunLike.coe.{succ u1, succ u3, succ u2} F H (fun (_x : H) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : H) => G) _x) (MulHomClass.toFunLike.{u1, u3, u2} F H G (MulOneClass.toMul.{u3} H (Monoid.toMulOneClass.{u3} H (DivInvMonoid.toMonoid.{u3} H (Group.toDivInvMonoid.{u3} H _inst_5)))) (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F H G (Monoid.toMulOneClass.{u3} H (DivInvMonoid.toMonoid.{u3} H (Group.toDivInvMonoid.{u3} H _inst_5))) (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))) _inst_6)) f) _inst_1) _inst_5
Case conversion may be inaccurate. Consider using '#align topological_group_induced topologicalGroup_inducedₓ'. -/
@[to_additive]
protected theorem topologicalGroup_induced {F : Type _} [Group H] [MonoidHomClass F H G] (f : F) :
    @TopologicalGroup H (induced f ‹_›) _ :=
  letI := induced f ‹_›
  Inducing.topologicalGroup f ⟨rfl⟩
#align topological_group_induced topologicalGroup_induced
#align topological_add_group_induced topologicalAddGroup_induced

namespace Subgroup

@[to_additive]
instance (S : Subgroup G) : TopologicalGroup S :=
  Inducing.topologicalGroup S.Subtype inducing_subtype_val

end Subgroup

#print Subgroup.topologicalClosure /-
/-- The (topological-space) closure of a subgroup of a space `M` with `has_continuous_mul` is
itself a subgroup. -/
@[to_additive
      "The (topological-space) closure of an additive subgroup of a space `M` with\n`has_continuous_add` is itself an additive subgroup."]
def Subgroup.topologicalClosure (s : Subgroup G) : Subgroup G :=
  {
    s.toSubmonoid.topologicalClosure with
    carrier := closure (s : Set G)
    inv_mem' := fun g m => by simpa [← Set.mem_inv, inv_closure] using m }
#align subgroup.topological_closure Subgroup.topologicalClosure
#align add_subgroup.topological_closure AddSubgroup.topologicalClosure
-/

/- warning: subgroup.topological_closure_coe -> Subgroup.topologicalClosure_coe is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] {s : Subgroup.{u1} G _inst_2}, Eq.{succ u1} (Set.{u1} G) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subgroup.{u1} G _inst_2) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)))) (Subgroup.topologicalClosure.{u1} G _inst_1 _inst_2 _inst_3 s)) (closure.{u1} G _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subgroup.{u1} G _inst_2) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)))) s))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] {s : Subgroup.{u1} G _inst_2}, Eq.{succ u1} (Set.{u1} G) (SetLike.coe.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2) (Subgroup.topologicalClosure.{u1} G _inst_1 _inst_2 _inst_3 s)) (closure.{u1} G _inst_1 (SetLike.coe.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2) s))
Case conversion may be inaccurate. Consider using '#align subgroup.topological_closure_coe Subgroup.topologicalClosure_coeₓ'. -/
@[simp, to_additive]
theorem Subgroup.topologicalClosure_coe {s : Subgroup G} :
    (s.topologicalClosure : Set G) = closure s :=
  rfl
#align subgroup.topological_closure_coe Subgroup.topologicalClosure_coe
#align add_subgroup.topological_closure_coe AddSubgroup.topologicalClosure_coe

/- warning: subgroup.le_topological_closure -> Subgroup.le_topologicalClosure is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] (s : Subgroup.{u1} G _inst_2), LE.le.{u1} (Subgroup.{u1} G _inst_2) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_2) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_2) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)))) s (Subgroup.topologicalClosure.{u1} G _inst_1 _inst_2 _inst_3 s)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] (s : Subgroup.{u1} G _inst_2), LE.le.{u1} (Subgroup.{u1} G _inst_2) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_2) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subgroup.{u1} G _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subgroup.{u1} G _inst_2) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_2))))) s (Subgroup.topologicalClosure.{u1} G _inst_1 _inst_2 _inst_3 s)
Case conversion may be inaccurate. Consider using '#align subgroup.le_topological_closure Subgroup.le_topologicalClosureₓ'. -/
@[to_additive]
theorem Subgroup.le_topologicalClosure (s : Subgroup G) : s ≤ s.topologicalClosure :=
  subset_closure
#align subgroup.le_topological_closure Subgroup.le_topologicalClosure
#align add_subgroup.le_topological_closure AddSubgroup.le_topologicalClosure

/- warning: subgroup.is_closed_topological_closure -> Subgroup.isClosed_topologicalClosure is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] (s : Subgroup.{u1} G _inst_2), IsClosed.{u1} G _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subgroup.{u1} G _inst_2) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)))) (Subgroup.topologicalClosure.{u1} G _inst_1 _inst_2 _inst_3 s))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] (s : Subgroup.{u1} G _inst_2), IsClosed.{u1} G _inst_1 (SetLike.coe.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2) (Subgroup.topologicalClosure.{u1} G _inst_1 _inst_2 _inst_3 s))
Case conversion may be inaccurate. Consider using '#align subgroup.is_closed_topological_closure Subgroup.isClosed_topologicalClosureₓ'. -/
@[to_additive]
theorem Subgroup.isClosed_topologicalClosure (s : Subgroup G) :
    IsClosed (s.topologicalClosure : Set G) := by convert isClosed_closure
#align subgroup.is_closed_topological_closure Subgroup.isClosed_topologicalClosure
#align add_subgroup.is_closed_topological_closure AddSubgroup.isClosed_topologicalClosure

/- warning: subgroup.topological_closure_minimal -> Subgroup.topologicalClosure_minimal is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] (s : Subgroup.{u1} G _inst_2) {t : Subgroup.{u1} G _inst_2}, (LE.le.{u1} (Subgroup.{u1} G _inst_2) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_2) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_2) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)))) s t) -> (IsClosed.{u1} G _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subgroup.{u1} G _inst_2) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)))) t)) -> (LE.le.{u1} (Subgroup.{u1} G _inst_2) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_2) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_2) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)))) (Subgroup.topologicalClosure.{u1} G _inst_1 _inst_2 _inst_3 s) t)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] (s : Subgroup.{u1} G _inst_2) {t : Subgroup.{u1} G _inst_2}, (LE.le.{u1} (Subgroup.{u1} G _inst_2) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_2) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subgroup.{u1} G _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subgroup.{u1} G _inst_2) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_2))))) s t) -> (IsClosed.{u1} G _inst_1 (SetLike.coe.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2) t)) -> (LE.le.{u1} (Subgroup.{u1} G _inst_2) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_2) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subgroup.{u1} G _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subgroup.{u1} G _inst_2) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_2))))) (Subgroup.topologicalClosure.{u1} G _inst_1 _inst_2 _inst_3 s) t)
Case conversion may be inaccurate. Consider using '#align subgroup.topological_closure_minimal Subgroup.topologicalClosure_minimalₓ'. -/
@[to_additive]
theorem Subgroup.topologicalClosure_minimal (s : Subgroup G) {t : Subgroup G} (h : s ≤ t)
    (ht : IsClosed (t : Set G)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht
#align subgroup.topological_closure_minimal Subgroup.topologicalClosure_minimal
#align add_subgroup.topological_closure_minimal AddSubgroup.topologicalClosure_minimal

/- warning: dense_range.topological_closure_map_subgroup -> DenseRange.topologicalClosure_map_subgroup is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] [_inst_5 : Group.{u2} H] [_inst_6 : TopologicalSpace.{u2} H] [_inst_7 : TopologicalGroup.{u2} H _inst_6 _inst_5] {f : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_5)))}, (Continuous.{u1, u2} G H _inst_1 _inst_6 (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_5)))) (fun (_x : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_5)))) => G -> H) (MonoidHom.hasCoeToFun.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_5)))) f)) -> (DenseRange.{u2, u1} H _inst_6 G (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_5)))) (fun (_x : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_5)))) => G -> H) (MonoidHom.hasCoeToFun.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_5)))) f)) -> (forall {s : Subgroup.{u1} G _inst_2}, (Eq.{succ u1} (Subgroup.{u1} G _inst_2) (Subgroup.topologicalClosure.{u1} G _inst_1 _inst_2 _inst_3 s) (Top.top.{u1} (Subgroup.{u1} G _inst_2) (Subgroup.hasTop.{u1} G _inst_2))) -> (Eq.{succ u2} (Subgroup.{u2} H _inst_5) (Subgroup.topologicalClosure.{u2} H _inst_6 _inst_5 _inst_7 (Subgroup.map.{u1, u2} G _inst_2 H _inst_5 f s)) (Top.top.{u2} (Subgroup.{u2} H _inst_5) (Subgroup.hasTop.{u2} H _inst_5))))
but is expected to have type
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] [_inst_5 : Group.{u2} H] [_inst_6 : TopologicalSpace.{u2} H] [_inst_7 : TopologicalGroup.{u2} H _inst_6 _inst_5] {f : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_5)))}, (Continuous.{u1, u2} G H _inst_1 _inst_6 (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_5)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : G) => H) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_5)))) G H (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_5)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_5)))) G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_5))) (MonoidHom.monoidHomClass.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_5)))))) f)) -> (DenseRange.{u2, u1} H _inst_6 G (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_5)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : G) => H) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_5)))) G H (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_5)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_5)))) G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_5))) (MonoidHom.monoidHomClass.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_5)))))) f)) -> (forall {s : Subgroup.{u1} G _inst_2}, (Eq.{succ u1} (Subgroup.{u1} G _inst_2) (Subgroup.topologicalClosure.{u1} G _inst_1 _inst_2 _inst_3 s) (Top.top.{u1} (Subgroup.{u1} G _inst_2) (Subgroup.instTopSubgroup.{u1} G _inst_2))) -> (Eq.{succ u2} (Subgroup.{u2} H _inst_5) (Subgroup.topologicalClosure.{u2} H _inst_6 _inst_5 _inst_7 (Subgroup.map.{u1, u2} G _inst_2 H _inst_5 f s)) (Top.top.{u2} (Subgroup.{u2} H _inst_5) (Subgroup.instTopSubgroup.{u2} H _inst_5))))
Case conversion may be inaccurate. Consider using '#align dense_range.topological_closure_map_subgroup DenseRange.topologicalClosure_map_subgroupₓ'. -/
@[to_additive]
theorem DenseRange.topologicalClosure_map_subgroup [Group H] [TopologicalSpace H]
    [TopologicalGroup H] {f : G →* H} (hf : Continuous f) (hf' : DenseRange f) {s : Subgroup G}
    (hs : s.topologicalClosure = ⊤) : (s.map f).topologicalClosure = ⊤ :=
  by
  rw [SetLike.ext'_iff] at hs⊢
  simp only [Subgroup.topologicalClosure_coe, Subgroup.coe_top, ← dense_iff_closure_eq] at hs⊢
  exact hf'.dense_image hf hs
#align dense_range.topological_closure_map_subgroup DenseRange.topologicalClosure_map_subgroup
#align dense_range.topological_closure_map_add_subgroup DenseRange.topologicalClosure_map_addSubgroup

#print Subgroup.is_normal_topologicalClosure /-
/-- The topological closure of a normal subgroup is normal.-/
@[to_additive "The topological closure of a normal additive subgroup is normal."]
theorem Subgroup.is_normal_topologicalClosure {G : Type _} [TopologicalSpace G] [Group G]
    [TopologicalGroup G] (N : Subgroup G) [N.Normal] : (Subgroup.topologicalClosure N).Normal :=
  {
    conj_mem := fun n hn g =>
      by
      apply map_mem_closure (TopologicalGroup.continuous_conj g) hn
      exact fun m hm => Subgroup.Normal.conj_mem inferInstance m hm g }
#align subgroup.is_normal_topological_closure Subgroup.is_normal_topologicalClosure
#align add_subgroup.is_normal_topological_closure AddSubgroup.is_normal_topologicalClosure
-/

/- warning: mul_mem_connected_component_one -> mul_mem_connectedComponent_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_5 : TopologicalSpace.{u1} G] [_inst_6 : MulOneClass.{u1} G] [_inst_7 : ContinuousMul.{u1} G _inst_5 (MulOneClass.toHasMul.{u1} G _inst_6)] {g : G} {h : G}, (Membership.Mem.{u1, u1} G (Set.{u1} G) (Set.hasMem.{u1} G) g (connectedComponent.{u1} G _inst_5 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G _inst_6)))))) -> (Membership.Mem.{u1, u1} G (Set.{u1} G) (Set.hasMem.{u1} G) h (connectedComponent.{u1} G _inst_5 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G _inst_6)))))) -> (Membership.Mem.{u1, u1} G (Set.{u1} G) (Set.hasMem.{u1} G) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G _inst_6)) g h) (connectedComponent.{u1} G _inst_5 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G _inst_6))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_5 : TopologicalSpace.{u1} G] [_inst_6 : MulOneClass.{u1} G] [_inst_7 : ContinuousMul.{u1} G _inst_5 (MulOneClass.toMul.{u1} G _inst_6)] {g : G} {h : G}, (Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) g (connectedComponent.{u1} G _inst_5 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (MulOneClass.toOne.{u1} G _inst_6))))) -> (Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) h (connectedComponent.{u1} G _inst_5 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (MulOneClass.toOne.{u1} G _inst_6))))) -> (Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G _inst_6)) g h) (connectedComponent.{u1} G _inst_5 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (MulOneClass.toOne.{u1} G _inst_6)))))
Case conversion may be inaccurate. Consider using '#align mul_mem_connected_component_one mul_mem_connectedComponent_oneₓ'. -/
@[to_additive]
theorem mul_mem_connectedComponent_one {G : Type _} [TopologicalSpace G] [MulOneClass G]
    [ContinuousMul G] {g h : G} (hg : g ∈ connectedComponent (1 : G))
    (hh : h ∈ connectedComponent (1 : G)) : g * h ∈ connectedComponent (1 : G) :=
  by
  rw [connectedComponent_eq hg]
  have hmul : g ∈ connectedComponent (g * h) :=
    by
    apply Continuous.image_connectedComponent_subset (continuous_mul_left g)
    rw [← connectedComponent_eq hh]
    exact ⟨(1 : G), mem_connectedComponent, by simp only [mul_one]⟩
  simpa [← connectedComponent_eq hmul] using mem_connectedComponent
#align mul_mem_connected_component_one mul_mem_connectedComponent_one
#align add_mem_connected_component_zero add_mem_connectedComponent_zero

/- warning: inv_mem_connected_component_one -> inv_mem_connectedComponent_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_5 : TopologicalSpace.{u1} G] [_inst_6 : Group.{u1} G] [_inst_7 : TopologicalGroup.{u1} G _inst_5 _inst_6] {g : G}, (Membership.Mem.{u1, u1} G (Set.{u1} G) (Set.hasMem.{u1} G) g (connectedComponent.{u1} G _inst_5 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_6))))))))) -> (Membership.Mem.{u1, u1} G (Set.{u1} G) (Set.hasMem.{u1} G) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_6)) g) (connectedComponent.{u1} G _inst_5 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_6)))))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_5 : TopologicalSpace.{u1} G] [_inst_6 : Group.{u1} G] [_inst_7 : TopologicalGroup.{u1} G _inst_5 _inst_6] {g : G}, (Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) g (connectedComponent.{u1} G _inst_5 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_6)))))))) -> (Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_6)))) g) (connectedComponent.{u1} G _inst_5 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_6))))))))
Case conversion may be inaccurate. Consider using '#align inv_mem_connected_component_one inv_mem_connectedComponent_oneₓ'. -/
@[to_additive]
theorem inv_mem_connectedComponent_one {G : Type _} [TopologicalSpace G] [Group G]
    [TopologicalGroup G] {g : G} (hg : g ∈ connectedComponent (1 : G)) :
    g⁻¹ ∈ connectedComponent (1 : G) := by
  rw [← inv_one]
  exact
    Continuous.image_connectedComponent_subset continuous_inv _
      ((Set.mem_image _ _ _).mp ⟨g, hg, rfl⟩)
#align inv_mem_connected_component_one inv_mem_connectedComponent_one
#align neg_mem_connected_component_zero neg_mem_connectedComponent_zero

#print Subgroup.connectedComponentOfOne /-
/-- The connected component of 1 is a subgroup of `G`. -/
@[to_additive "The connected component of 0 is a subgroup of `G`."]
def Subgroup.connectedComponentOfOne (G : Type _) [TopologicalSpace G] [Group G]
    [TopologicalGroup G] : Subgroup G
    where
  carrier := connectedComponent (1 : G)
  one_mem' := mem_connectedComponent
  mul_mem' g h hg hh := mul_mem_connectedComponent_one hg hh
  inv_mem' g hg := inv_mem_connectedComponent_one hg
#align subgroup.connected_component_of_one Subgroup.connectedComponentOfOne
#align add_subgroup.connected_component_of_zero AddSubgroup.connectedComponentOfZero
-/

/- warning: subgroup.comm_group_topological_closure -> Subgroup.commGroupTopologicalClosure is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] [_inst_5 : T2Space.{u1} G _inst_1] (s : Subgroup.{u1} G _inst_2), (forall (x : coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) s) (y : coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) s), Eq.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) s) (HMul.hMul.{u1, u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) s) (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) s) (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) s) (instHMul.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) s) (Subgroup.mul.{u1} G _inst_2 s)) x y) (HMul.hMul.{u1, u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) s) (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) s) (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) s) (instHMul.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) s) (Subgroup.mul.{u1} G _inst_2 s)) y x)) -> (CommGroup.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) (Subgroup.topologicalClosure.{u1} G _inst_1 _inst_2 _inst_3 s)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] [_inst_5 : T2Space.{u1} G _inst_1] (s : Subgroup.{u1} G _inst_2), (forall (x : Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x s)) (y : Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x s)), Eq.{succ u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x s)) (HMul.hMul.{u1, u1, u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x s)) (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x s)) (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x s)) (instHMul.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x s)) (Subgroup.mul.{u1} G _inst_2 s)) x y) (HMul.hMul.{u1, u1, u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x s)) (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x s)) (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x s)) (instHMul.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x s)) (Subgroup.mul.{u1} G _inst_2 s)) y x)) -> (CommGroup.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x (Subgroup.topologicalClosure.{u1} G _inst_1 _inst_2 _inst_3 s))))
Case conversion may be inaccurate. Consider using '#align subgroup.comm_group_topological_closure Subgroup.commGroupTopologicalClosureₓ'. -/
/-- If a subgroup of a topological group is commutative, then so is its topological closure. -/
@[to_additive
      "If a subgroup of an additive topological group is commutative, then so is its\ntopological closure."]
def Subgroup.commGroupTopologicalClosure [T2Space G] (s : Subgroup G)
    (hs : ∀ x y : s, x * y = y * x) : CommGroup s.topologicalClosure :=
  { s.topologicalClosure.toGroup, s.toSubmonoid.commMonoidTopologicalClosure hs with }
#align subgroup.comm_group_topological_closure Subgroup.commGroupTopologicalClosure
#align add_subgroup.add_comm_group_topological_closure AddSubgroup.addCommGroupTopologicalClosure

/- warning: exists_nhds_split_inv -> exists_nhds_split_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] {s : Set.{u1} G}, (Membership.Mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (Filter.hasMem.{u1} G) s (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))))))) -> (Exists.{succ u1} (Set.{u1} G) (fun (V : Set.{u1} G) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (Filter.hasMem.{u1} G) V (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))))))) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (Filter.hasMem.{u1} G) V (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))))))) => forall (v : G), (Membership.Mem.{u1, u1} G (Set.{u1} G) (Set.hasMem.{u1} G) v V) -> (forall (w : G), (Membership.Mem.{u1, u1} G (Set.{u1} G) (Set.hasMem.{u1} G) w V) -> (Membership.Mem.{u1, u1} G (Set.{u1} G) (Set.hasMem.{u1} G) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) v w) s)))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] {s : Set.{u1} G}, (Membership.mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (instMembershipSetFilter.{u1} G) s (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))))))) -> (Exists.{succ u1} (Set.{u1} G) (fun (V : Set.{u1} G) => And (Membership.mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (instMembershipSetFilter.{u1} G) V (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))))))) (forall (v : G), (Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) v V) -> (forall (w : G), (Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) w V) -> (Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) v w) s)))))
Case conversion may be inaccurate. Consider using '#align exists_nhds_split_inv exists_nhds_split_invₓ'. -/
@[to_additive exists_nhds_half_neg]
theorem exists_nhds_split_inv {s : Set G} (hs : s ∈ 𝓝 (1 : G)) :
    ∃ V ∈ 𝓝 (1 : G), ∀ v ∈ V, ∀ w ∈ V, v / w ∈ s :=
  by
  have : (fun p : G × G => p.1 * p.2⁻¹) ⁻¹' s ∈ 𝓝 ((1, 1) : G × G) :=
    continuousAt_fst.mul continuousAt_snd.inv (by simpa)
  simpa only [div_eq_mul_inv, nhds_prod_eq, mem_prod_self_iff, prod_subset_iff, mem_preimage] using
    this
#align exists_nhds_split_inv exists_nhds_split_inv
#align exists_nhds_half_neg exists_nhds_half_neg

/- warning: nhds_translation_mul_inv -> nhds_translation_mul_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] (x : G), Eq.{succ u1} (Filter.{u1} G) (Filter.comap.{u1, u1} G G (fun (y : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) y (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) x)) (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))))))) (nhds.{u1} G _inst_1 x)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] (x : G), Eq.{succ u1} (Filter.{u1} G) (Filter.comap.{u1, u1} G G (fun (y : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) y (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))) x)) (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))))))) (nhds.{u1} G _inst_1 x)
Case conversion may be inaccurate. Consider using '#align nhds_translation_mul_inv nhds_translation_mul_invₓ'. -/
@[to_additive]
theorem nhds_translation_mul_inv (x : G) : comap (fun y : G => y * x⁻¹) (𝓝 1) = 𝓝 x :=
  ((Homeomorph.mulRight x⁻¹).comap_nhds_eq 1).trans <| show 𝓝 (1 * x⁻¹⁻¹) = 𝓝 x by simp
#align nhds_translation_mul_inv nhds_translation_mul_inv
#align nhds_translation_add_neg nhds_translation_add_neg

/- warning: map_mul_left_nhds -> map_mul_left_nhds is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] (x : G) (y : G), Eq.{succ u1} (Filter.{u1} G) (Filter.map.{u1, u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) x) (nhds.{u1} G _inst_1 y)) (nhds.{u1} G _inst_1 (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) x y))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] (x : G) (y : G), Eq.{succ u1} (Filter.{u1} G) (Filter.map.{u1, u1} G G ((fun (x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.5920 : G) (x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.5922 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.5920 x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.5922) x) (nhds.{u1} G _inst_1 y)) (nhds.{u1} G _inst_1 (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) x y))
Case conversion may be inaccurate. Consider using '#align map_mul_left_nhds map_mul_left_nhdsₓ'. -/
@[simp, to_additive]
theorem map_mul_left_nhds (x y : G) : map ((· * ·) x) (𝓝 y) = 𝓝 (x * y) :=
  (Homeomorph.mulLeft x).map_nhds_eq y
#align map_mul_left_nhds map_mul_left_nhds
#align map_add_left_nhds map_add_left_nhds

/- warning: map_mul_left_nhds_one -> map_mul_left_nhds_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] (x : G), Eq.{succ u1} (Filter.{u1} G) (Filter.map.{u1, u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) x) (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))))))) (nhds.{u1} G _inst_1 x)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] (x : G), Eq.{succ u1} (Filter.{u1} G) (Filter.map.{u1, u1} G G ((fun (x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.5993 : G) (x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.5995 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.5993 x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.5995) x) (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))))))) (nhds.{u1} G _inst_1 x)
Case conversion may be inaccurate. Consider using '#align map_mul_left_nhds_one map_mul_left_nhds_oneₓ'. -/
@[to_additive]
theorem map_mul_left_nhds_one (x : G) : map ((· * ·) x) (𝓝 1) = 𝓝 x := by simp
#align map_mul_left_nhds_one map_mul_left_nhds_one
#align map_add_left_nhds_zero map_add_left_nhds_zero

/- warning: map_mul_right_nhds -> map_mul_right_nhds is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] (x : G) (y : G), Eq.{succ u1} (Filter.{u1} G) (Filter.map.{u1, u1} G G (fun (z : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) z x) (nhds.{u1} G _inst_1 y)) (nhds.{u1} G _inst_1 (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) y x))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] (x : G) (y : G), Eq.{succ u1} (Filter.{u1} G) (Filter.map.{u1, u1} G G (fun (z : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) z x) (nhds.{u1} G _inst_1 y)) (nhds.{u1} G _inst_1 (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) y x))
Case conversion may be inaccurate. Consider using '#align map_mul_right_nhds map_mul_right_nhdsₓ'. -/
@[simp, to_additive]
theorem map_mul_right_nhds (x y : G) : map (fun z => z * x) (𝓝 y) = 𝓝 (y * x) :=
  (Homeomorph.mulRight x).map_nhds_eq y
#align map_mul_right_nhds map_mul_right_nhds
#align map_add_right_nhds map_add_right_nhds

/- warning: map_mul_right_nhds_one -> map_mul_right_nhds_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] (x : G), Eq.{succ u1} (Filter.{u1} G) (Filter.map.{u1, u1} G G (fun (y : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) y x) (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))))))) (nhds.{u1} G _inst_1 x)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] (x : G), Eq.{succ u1} (Filter.{u1} G) (Filter.map.{u1, u1} G G (fun (y : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) y x) (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))))))) (nhds.{u1} G _inst_1 x)
Case conversion may be inaccurate. Consider using '#align map_mul_right_nhds_one map_mul_right_nhds_oneₓ'. -/
@[to_additive]
theorem map_mul_right_nhds_one (x : G) : map (fun y => y * x) (𝓝 1) = 𝓝 x := by simp
#align map_mul_right_nhds_one map_mul_right_nhds_one
#align map_add_right_nhds_zero map_add_right_nhds_zero

/- warning: filter.has_basis.nhds_of_one -> Filter.HasBasis.nhds_of_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] {ι : Sort.{u2}} {p : ι -> Prop} {s : ι -> (Set.{u1} G)}, (Filter.HasBasis.{u1, u2} G ι (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))))) p s) -> (forall (x : G), Filter.HasBasis.{u1, u2} G ι (nhds.{u1} G _inst_1 x) p (fun (i : ι) => setOf.{u1} G (fun (y : G) => Membership.Mem.{u1, u1} G (Set.{u1} G) (Set.hasMem.{u1} G) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) y x) (s i))))
but is expected to have type
  forall {G : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} G] [_inst_2 : Group.{u2} G] [_inst_3 : TopologicalGroup.{u2} G _inst_1 _inst_2] {ι : Sort.{u1}} {p : ι -> Prop} {s : ι -> (Set.{u2} G)}, (Filter.HasBasis.{u2, u1} G ι (nhds.{u2} G _inst_1 (OfNat.ofNat.{u2} G 1 (One.toOfNat1.{u2} G (InvOneClass.toOne.{u2} G (DivInvOneMonoid.toInvOneClass.{u2} G (DivisionMonoid.toDivInvOneMonoid.{u2} G (Group.toDivisionMonoid.{u2} G _inst_2))))))) p s) -> (forall (x : G), Filter.HasBasis.{u2, u1} G ι (nhds.{u2} G _inst_1 x) p (fun (i : ι) => setOf.{u2} G (fun (y : G) => Membership.mem.{u2, u2} G (Set.{u2} G) (Set.instMembershipSet.{u2} G) (HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G (DivInvMonoid.toDiv.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))) y x) (s i))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.nhds_of_one Filter.HasBasis.nhds_of_oneₓ'. -/
@[to_additive]
theorem Filter.HasBasis.nhds_of_one {ι : Sort _} {p : ι → Prop} {s : ι → Set G}
    (hb : HasBasis (𝓝 1 : Filter G) p s) (x : G) : HasBasis (𝓝 x) p fun i => { y | y / x ∈ s i } :=
  by
  rw [← nhds_translation_mul_inv]
  simp_rw [div_eq_mul_inv]
  exact hb.comap _
#align filter.has_basis.nhds_of_one Filter.HasBasis.nhds_of_one
#align filter.has_basis.nhds_of_zero Filter.HasBasis.nhds_of_zero

/- warning: mem_closure_iff_nhds_one -> mem_closure_iff_nhds_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] {x : G} {s : Set.{u1} G}, Iff (Membership.Mem.{u1, u1} G (Set.{u1} G) (Set.hasMem.{u1} G) x (closure.{u1} G _inst_1 s)) (forall (U : Set.{u1} G), (Membership.Mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (Filter.hasMem.{u1} G) U (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))))))) -> (Exists.{succ u1} G (fun (y : G) => Exists.{0} (Membership.Mem.{u1, u1} G (Set.{u1} G) (Set.hasMem.{u1} G) y s) (fun (H : Membership.Mem.{u1, u1} G (Set.{u1} G) (Set.hasMem.{u1} G) y s) => Membership.Mem.{u1, u1} G (Set.{u1} G) (Set.hasMem.{u1} G) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) y x) U))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] {x : G} {s : Set.{u1} G}, Iff (Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) x (closure.{u1} G _inst_1 s)) (forall (U : Set.{u1} G), (Membership.mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (instMembershipSetFilter.{u1} G) U (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))))))) -> (Exists.{succ u1} G (fun (y : G) => And (Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) y s) (Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) y x) U))))
Case conversion may be inaccurate. Consider using '#align mem_closure_iff_nhds_one mem_closure_iff_nhds_oneₓ'. -/
@[to_additive]
theorem mem_closure_iff_nhds_one {x : G} {s : Set G} :
    x ∈ closure s ↔ ∀ U ∈ (𝓝 1 : Filter G), ∃ y ∈ s, y / x ∈ U :=
  by
  rw [mem_closure_iff_nhds_basis ((𝓝 1 : Filter G).basis_sets.nhds_of_one x)]
  rfl
#align mem_closure_iff_nhds_one mem_closure_iff_nhds_one
#align mem_closure_iff_nhds_zero mem_closure_iff_nhds_zero

/- warning: continuous_of_continuous_at_one -> continuous_of_continuousAt_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] {M : Type.{u2}} {hom : Type.{u3}} [_inst_5 : MulOneClass.{u2} M] [_inst_6 : TopologicalSpace.{u2} M] [_inst_7 : ContinuousMul.{u2} M _inst_6 (MulOneClass.toHasMul.{u2} M _inst_5)] [_inst_8 : MonoidHomClass.{u3, u1, u2} hom G M (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) _inst_5] (f : hom), (ContinuousAt.{u1, u2} G M _inst_1 _inst_6 (coeFn.{succ u3, max (succ u1) (succ u2)} hom (fun (_x : hom) => G -> M) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} hom G (fun (_x : G) => M) (MulHomClass.toFunLike.{u3, u1, u2} hom G M (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) (MulOneClass.toHasMul.{u2} M _inst_5) (MonoidHomClass.toMulHomClass.{u3, u1, u2} hom G M (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) _inst_5 _inst_8))) f) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))))) -> (Continuous.{u1, u2} G M _inst_1 _inst_6 (coeFn.{succ u3, max (succ u1) (succ u2)} hom (fun (_x : hom) => G -> M) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} hom G (fun (_x : G) => M) (MulHomClass.toFunLike.{u3, u1, u2} hom G M (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) (MulOneClass.toHasMul.{u2} M _inst_5) (MonoidHomClass.toMulHomClass.{u3, u1, u2} hom G M (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) _inst_5 _inst_8))) f))
but is expected to have type
  forall {G : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} G] [_inst_2 : Group.{u3} G] [_inst_3 : TopologicalGroup.{u3} G _inst_1 _inst_2] {M : Type.{u2}} {hom : Type.{u1}} [_inst_5 : MulOneClass.{u2} M] [_inst_6 : TopologicalSpace.{u2} M] [_inst_7 : ContinuousMul.{u2} M _inst_6 (MulOneClass.toMul.{u2} M _inst_5)] [_inst_8 : MonoidHomClass.{u1, u3, u2} hom G M (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_2))) _inst_5] (f : hom), (ContinuousAt.{u3, u2} G M _inst_1 _inst_6 (FunLike.coe.{succ u1, succ u3, succ u2} hom G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : G) => M) _x) (MulHomClass.toFunLike.{u1, u3, u2} hom G M (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_2)))) (MulOneClass.toMul.{u2} M _inst_5) (MonoidHomClass.toMulHomClass.{u1, u3, u2} hom G M (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_2))) _inst_5 _inst_8)) f) (OfNat.ofNat.{u3} G 1 (One.toOfNat1.{u3} G (InvOneClass.toOne.{u3} G (DivInvOneMonoid.toInvOneClass.{u3} G (DivisionMonoid.toDivInvOneMonoid.{u3} G (Group.toDivisionMonoid.{u3} G _inst_2))))))) -> (Continuous.{u3, u2} G M _inst_1 _inst_6 (FunLike.coe.{succ u1, succ u3, succ u2} hom G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : G) => M) _x) (MulHomClass.toFunLike.{u1, u3, u2} hom G M (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_2)))) (MulOneClass.toMul.{u2} M _inst_5) (MonoidHomClass.toMulHomClass.{u1, u3, u2} hom G M (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_2))) _inst_5 _inst_8)) f))
Case conversion may be inaccurate. Consider using '#align continuous_of_continuous_at_one continuous_of_continuousAt_oneₓ'. -/
/-- A monoid homomorphism (a bundled morphism of a type that implements `monoid_hom_class`) from a
topological group to a topological monoid is continuous provided that it is continuous at one. See
also `uniform_continuous_of_continuous_at_one`. -/
@[to_additive
      "An additive monoid homomorphism (a bundled morphism of a type that implements\n`add_monoid_hom_class`) from an additive topological group to an additive topological monoid is\ncontinuous provided that it is continuous at zero. See also\n`uniform_continuous_of_continuous_at_zero`."]
theorem continuous_of_continuousAt_one {M hom : Type _} [MulOneClass M] [TopologicalSpace M]
    [ContinuousMul M] [MonoidHomClass hom G M] (f : hom) (hf : ContinuousAt f 1) : Continuous f :=
  continuous_iff_continuousAt.2 fun x => by
    simpa only [ContinuousAt, ← map_mul_left_nhds_one x, tendsto_map'_iff, (· ∘ ·), map_mul,
      map_one, mul_one] using hf.tendsto.const_mul (f x)
#align continuous_of_continuous_at_one continuous_of_continuousAt_one
#align continuous_of_continuous_at_zero continuous_of_continuousAt_zero

/- warning: topological_group.ext -> TopologicalGroup.ext is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_5 : Group.{u1} G] {t : TopologicalSpace.{u1} G} {t' : TopologicalSpace.{u1} G}, (TopologicalGroup.{u1} G t _inst_5) -> (TopologicalGroup.{u1} G t' _inst_5) -> (Eq.{succ u1} (Filter.{u1} G) (nhds.{u1} G t (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))))))) (nhds.{u1} G t' (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))))))) -> (Eq.{succ u1} (TopologicalSpace.{u1} G) t t')
but is expected to have type
  forall {G : Type.{u1}} [_inst_5 : Group.{u1} G] {t : TopologicalSpace.{u1} G} {t' : TopologicalSpace.{u1} G}, (TopologicalGroup.{u1} G t _inst_5) -> (TopologicalGroup.{u1} G t' _inst_5) -> (Eq.{succ u1} (Filter.{u1} G) (nhds.{u1} G t (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5))))))) (nhds.{u1} G t' (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5)))))))) -> (Eq.{succ u1} (TopologicalSpace.{u1} G) t t')
Case conversion may be inaccurate. Consider using '#align topological_group.ext TopologicalGroup.extₓ'. -/
@[to_additive]
theorem TopologicalGroup.ext {G : Type _} [Group G] {t t' : TopologicalSpace G}
    (tg : @TopologicalGroup G t _) (tg' : @TopologicalGroup G t' _)
    (h : @nhds G t 1 = @nhds G t' 1) : t = t' :=
  eq_of_nhds_eq_nhds fun x => by
    rw [← @nhds_translation_mul_inv G t _ _ x, ← @nhds_translation_mul_inv G t' _ _ x, ← h]
#align topological_group.ext TopologicalGroup.ext
#align topological_add_group.ext TopologicalAddGroup.ext

/- warning: topological_group.ext_iff -> TopologicalGroup.ext_iff is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_5 : Group.{u1} G] {t : TopologicalSpace.{u1} G} {t' : TopologicalSpace.{u1} G}, (TopologicalGroup.{u1} G t _inst_5) -> (TopologicalGroup.{u1} G t' _inst_5) -> (Iff (Eq.{succ u1} (TopologicalSpace.{u1} G) t t') (Eq.{succ u1} (Filter.{u1} G) (nhds.{u1} G t (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))))))) (nhds.{u1} G t' (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_5 : Group.{u1} G] {t : TopologicalSpace.{u1} G} {t' : TopologicalSpace.{u1} G}, (TopologicalGroup.{u1} G t _inst_5) -> (TopologicalGroup.{u1} G t' _inst_5) -> (Iff (Eq.{succ u1} (TopologicalSpace.{u1} G) t t') (Eq.{succ u1} (Filter.{u1} G) (nhds.{u1} G t (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5))))))) (nhds.{u1} G t' (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5)))))))))
Case conversion may be inaccurate. Consider using '#align topological_group.ext_iff TopologicalGroup.ext_iffₓ'. -/
@[to_additive]
theorem TopologicalGroup.ext_iff {G : Type _} [Group G] {t t' : TopologicalSpace G}
    (tg : @TopologicalGroup G t _) (tg' : @TopologicalGroup G t' _) :
    t = t' ↔ @nhds G t 1 = @nhds G t' 1 :=
  ⟨fun h => h ▸ rfl, tg.ext tg'⟩
#align topological_group.ext_iff TopologicalGroup.ext_iff
#align topological_add_group.ext_iff TopologicalAddGroup.ext_iff

/- warning: has_continuous_inv.of_nhds_one -> ContinuousInv.of_nhds_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_5 : Group.{u1} G] [_inst_6 : TopologicalSpace.{u1} G], (Filter.Tendsto.{u1, u1} G G (fun (x : G) => Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)) x) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))))))) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))))))) -> (forall (x₀ : G), Eq.{succ u1} (Filter.{u1} G) (nhds.{u1} G _inst_6 x₀) (Filter.map.{u1, u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))) x₀ x) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))))))))) -> (forall (x₀ : G), Filter.Tendsto.{u1, u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))) x₀ x) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)) x₀)) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))))))) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))))))) -> (ContinuousInv.{u1} G _inst_6 (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_5 : Group.{u1} G] [_inst_6 : TopologicalSpace.{u1} G], (Filter.Tendsto.{u1, u1} G G (fun (x : G) => Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5)))) x) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5))))))) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5)))))))) -> (forall (x₀ : G), Eq.{succ u1} (Filter.{u1} G) (nhds.{u1} G _inst_6 x₀) (Filter.map.{u1, u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))) x₀ x) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5))))))))) -> (forall (x₀ : G), Filter.Tendsto.{u1, u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))) x₀ x) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5)))) x₀)) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5))))))) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5)))))))) -> (ContinuousInv.{u1} G _inst_6 (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5)))))
Case conversion may be inaccurate. Consider using '#align has_continuous_inv.of_nhds_one ContinuousInv.of_nhds_oneₓ'. -/
@[to_additive]
theorem ContinuousInv.of_nhds_one {G : Type _} [Group G] [TopologicalSpace G]
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (fun x : G => x₀ * x) (𝓝 1))
    (hconj : ∀ x₀ : G, Tendsto (fun x : G => x₀ * x * x₀⁻¹) (𝓝 1) (𝓝 1)) : ContinuousInv G :=
  by
  refine' ⟨continuous_iff_continuousAt.2 fun x₀ => _⟩
  have : tendsto (fun x => x₀⁻¹ * (x₀ * x⁻¹ * x₀⁻¹)) (𝓝 1) (map ((· * ·) x₀⁻¹) (𝓝 1)) :=
    (tendsto_map.comp <| hconj x₀).comp hinv
  simpa only [ContinuousAt, hleft x₀, hleft x₀⁻¹, tendsto_map'_iff, (· ∘ ·), mul_assoc, mul_inv_rev,
    inv_mul_cancel_left] using this
#align has_continuous_inv.of_nhds_one ContinuousInv.of_nhds_one
#align has_continuous_neg.of_nhds_zero ContinuousNeg.of_nhds_zero

/- warning: topological_group.of_nhds_one' -> TopologicalGroup.of_nhds_one' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_5 : Group.{u1} G] [_inst_6 : TopologicalSpace.{u1} G], (Filter.Tendsto.{u1, u1} (Prod.{u1, u1} G G) G (Function.uncurry.{u1, u1, u1} G G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))))) (Filter.prod.{u1, u1} G G (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))))))) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))))))) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))))))) -> (Filter.Tendsto.{u1, u1} G G (fun (x : G) => Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)) x) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))))))) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))))))) -> (forall (x₀ : G), Eq.{succ u1} (Filter.{u1} G) (nhds.{u1} G _inst_6 x₀) (Filter.map.{u1, u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))) x₀ x) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))))))))) -> (forall (x₀ : G), Eq.{succ u1} (Filter.{u1} G) (nhds.{u1} G _inst_6 x₀) (Filter.map.{u1, u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))) x x₀) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))))))))) -> (TopologicalGroup.{u1} G _inst_6 _inst_5)
but is expected to have type
  forall {G : Type.{u1}} [_inst_5 : Group.{u1} G] [_inst_6 : TopologicalSpace.{u1} G], (Filter.Tendsto.{u1, u1} (Prod.{u1, u1} G G) G (Function.uncurry.{u1, u1, u1} G G G (fun (x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.7129 : G) (x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.7131 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))) x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.7129 x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.7131)) (Filter.prod.{u1, u1} G G (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5))))))) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5)))))))) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5)))))))) -> (Filter.Tendsto.{u1, u1} G G (fun (x : G) => Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5)))) x) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5))))))) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5)))))))) -> (forall (x₀ : G), Eq.{succ u1} (Filter.{u1} G) (nhds.{u1} G _inst_6 x₀) (Filter.map.{u1, u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))) x₀ x) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5))))))))) -> (forall (x₀ : G), Eq.{succ u1} (Filter.{u1} G) (nhds.{u1} G _inst_6 x₀) (Filter.map.{u1, u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))) x x₀) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5))))))))) -> (TopologicalGroup.{u1} G _inst_6 _inst_5)
Case conversion may be inaccurate. Consider using '#align topological_group.of_nhds_one' TopologicalGroup.of_nhds_one'ₓ'. -/
@[to_additive]
theorem TopologicalGroup.of_nhds_one' {G : Type u} [Group G] [TopologicalSpace G]
    (hmul : Tendsto (uncurry ((· * ·) : G → G → G)) (𝓝 1 ×ᶠ 𝓝 1) (𝓝 1))
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1))
    (hright : ∀ x₀ : G, 𝓝 x₀ = map (fun x => x * x₀) (𝓝 1)) : TopologicalGroup G :=
  { to_continuousMul := ContinuousMul.of_nhds_one hmul hleft hright
    to_continuousInv :=
      ContinuousInv.of_nhds_one hinv hleft fun x₀ =>
        le_of_eq
          (by
            rw [show (fun x => x₀ * x * x₀⁻¹) = (fun x => x * x₀⁻¹) ∘ fun x => x₀ * x from rfl, ←
              map_map, ← hleft, hright, map_map]
            simp [(· ∘ ·)]) }
#align topological_group.of_nhds_one' TopologicalGroup.of_nhds_one'
#align topological_add_group.of_nhds_zero' TopologicalAddGroup.of_nhds_zero'

/- warning: topological_group.of_nhds_one -> TopologicalGroup.of_nhds_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_5 : Group.{u1} G] [_inst_6 : TopologicalSpace.{u1} G], (Filter.Tendsto.{u1, u1} (Prod.{u1, u1} G G) G (Function.uncurry.{u1, u1, u1} G G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))))) (Filter.prod.{u1, u1} G G (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))))))) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))))))) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))))))) -> (Filter.Tendsto.{u1, u1} G G (fun (x : G) => Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)) x) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))))))) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))))))) -> (forall (x₀ : G), Eq.{succ u1} (Filter.{u1} G) (nhds.{u1} G _inst_6 x₀) (Filter.map.{u1, u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))) x₀ x) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))))))))) -> (forall (x₀ : G), Filter.Tendsto.{u1, u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))) x₀ x) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)) x₀)) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))))))) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))))))) -> (TopologicalGroup.{u1} G _inst_6 _inst_5)
but is expected to have type
  forall {G : Type.{u1}} [_inst_5 : Group.{u1} G] [_inst_6 : TopologicalSpace.{u1} G], (Filter.Tendsto.{u1, u1} (Prod.{u1, u1} G G) G (Function.uncurry.{u1, u1, u1} G G G (fun (x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.7417 : G) (x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.7419 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))) x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.7417 x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.7419)) (Filter.prod.{u1, u1} G G (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5))))))) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5)))))))) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5)))))))) -> (Filter.Tendsto.{u1, u1} G G (fun (x : G) => Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5)))) x) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5))))))) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5)))))))) -> (forall (x₀ : G), Eq.{succ u1} (Filter.{u1} G) (nhds.{u1} G _inst_6 x₀) (Filter.map.{u1, u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))) x₀ x) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5))))))))) -> (forall (x₀ : G), Filter.Tendsto.{u1, u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))))) x₀ x) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5)))) x₀)) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5))))))) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_5)))))))) -> (TopologicalGroup.{u1} G _inst_6 _inst_5)
Case conversion may be inaccurate. Consider using '#align topological_group.of_nhds_one TopologicalGroup.of_nhds_oneₓ'. -/
@[to_additive]
theorem TopologicalGroup.of_nhds_one {G : Type u} [Group G] [TopologicalSpace G]
    (hmul : Tendsto (uncurry ((· * ·) : G → G → G)) (𝓝 1 ×ᶠ 𝓝 1) (𝓝 1))
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1))
    (hconj : ∀ x₀ : G, Tendsto (fun x => x₀ * x * x₀⁻¹) (𝓝 1) (𝓝 1)) : TopologicalGroup G :=
  by
  refine' TopologicalGroup.of_nhds_one' hmul hinv hleft fun x₀ => _
  replace hconj : ∀ x₀ : G, map (fun x => x₀ * x * x₀⁻¹) (𝓝 1) = 𝓝 1
  exact fun x₀ =>
    map_eq_of_inverse (fun x => x₀⁻¹ * x * x₀⁻¹⁻¹)
      (by
        ext
        simp [mul_assoc])
      (hconj _) (hconj _)
  rw [← hconj x₀]
  simpa [(· ∘ ·)] using hleft _
#align topological_group.of_nhds_one TopologicalGroup.of_nhds_one
#align topological_add_group.of_nhds_zero TopologicalAddGroup.of_nhds_zero

/- warning: topological_group.of_comm_of_nhds_one -> TopologicalGroup.of_comm_of_nhds_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_5 : CommGroup.{u1} G] [_inst_6 : TopologicalSpace.{u1} G], (Filter.Tendsto.{u1, u1} (Prod.{u1, u1} G G) G (Function.uncurry.{u1, u1, u1} G G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_5)))))))) (Filter.prod.{u1, u1} G G (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_5))))))))) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_5)))))))))) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_5)))))))))) -> (Filter.Tendsto.{u1, u1} G G (fun (x : G) => Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_5))) x) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_5))))))))) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_5)))))))))) -> (forall (x₀ : G), Eq.{succ u1} (Filter.{u1} G) (nhds.{u1} G _inst_6 x₀) (Filter.map.{u1, u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_5)))))) x₀ x) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_5))))))))))) -> (TopologicalGroup.{u1} G _inst_6 (CommGroup.toGroup.{u1} G _inst_5))
but is expected to have type
  forall {G : Type.{u1}} [_inst_5 : CommGroup.{u1} G] [_inst_6 : TopologicalSpace.{u1} G], (Filter.Tendsto.{u1, u1} (Prod.{u1, u1} G G) G (Function.uncurry.{u1, u1, u1} G G G (fun (x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.7733 : G) (x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.7735 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_5)))))) x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.7733 x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.7735)) (Filter.prod.{u1, u1} G G (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_5)))))))) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_5))))))))) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_5))))))))) -> (Filter.Tendsto.{u1, u1} G G (fun (x : G) => Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_5))))) x) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_5)))))))) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_5))))))))) -> (forall (x₀ : G), Eq.{succ u1} (Filter.{u1} G) (nhds.{u1} G _inst_6 x₀) (Filter.map.{u1, u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_5)))))) x₀ x) (nhds.{u1} G _inst_6 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_5)))))))))) -> (TopologicalGroup.{u1} G _inst_6 (CommGroup.toGroup.{u1} G _inst_5))
Case conversion may be inaccurate. Consider using '#align topological_group.of_comm_of_nhds_one TopologicalGroup.of_comm_of_nhds_oneₓ'. -/
@[to_additive]
theorem TopologicalGroup.of_comm_of_nhds_one {G : Type u} [CommGroup G] [TopologicalSpace G]
    (hmul : Tendsto (uncurry ((· * ·) : G → G → G)) (𝓝 1 ×ᶠ 𝓝 1) (𝓝 1))
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1)) : TopologicalGroup G :=
  TopologicalGroup.of_nhds_one hmul hinv hleft (by simpa using tendsto_id)
#align topological_group.of_comm_of_nhds_one TopologicalGroup.of_comm_of_nhds_one
#align topological_add_group.of_comm_of_nhds_zero TopologicalAddGroup.of_comm_of_nhds_zero

end TopologicalGroup

section QuotientTopologicalGroup

variable [TopologicalSpace G] [Group G] [TopologicalGroup G] (N : Subgroup G) (n : N.Normal)

#print QuotientGroup.Quotient.topologicalSpace /-
@[to_additive]
instance QuotientGroup.Quotient.topologicalSpace {G : Type _} [Group G] [TopologicalSpace G]
    (N : Subgroup G) : TopologicalSpace (G ⧸ N) :=
  Quotient.topologicalSpace
#align quotient_group.quotient.topological_space QuotientGroup.Quotient.topologicalSpace
#align quotient_add_group.quotient.topological_space QuotientAddGroup.Quotient.topologicalSpace
-/

open QuotientGroup

#print QuotientGroup.isOpenMap_coe /-
@[to_additive]
theorem QuotientGroup.isOpenMap_coe : IsOpenMap (coe : G → G ⧸ N) :=
  by
  intro s s_op
  change IsOpen ((coe : G → G ⧸ N) ⁻¹' (coe '' s))
  rw [QuotientGroup.preimage_image_mk N s]
  exact isOpen_unionᵢ fun n => (continuous_mul_right _).isOpen_preimage s s_op
#align quotient_group.is_open_map_coe QuotientGroup.isOpenMap_coe
#align quotient_add_group.is_open_map_coe QuotientAddGroup.isOpenMap_coe
-/

#print topologicalGroup_quotient /-
@[to_additive]
instance topologicalGroup_quotient [N.Normal] : TopologicalGroup (G ⧸ N)
    where
  continuous_mul :=
    by
    have cont : Continuous ((coe : G → G ⧸ N) ∘ fun p : G × G => p.fst * p.snd) :=
      continuous_quot_mk.comp continuous_mul
    have quot : QuotientMap fun p : G × G => ((p.1 : G ⧸ N), (p.2 : G ⧸ N)) :=
      by
      apply IsOpenMap.to_quotientMap
      · exact (QuotientGroup.isOpenMap_coe N).Prod (QuotientGroup.isOpenMap_coe N)
      · exact continuous_quot_mk.prod_map continuous_quot_mk
      · exact (surjective_quot_mk _).Prod_map (surjective_quot_mk _)
    exact (QuotientMap.continuous_iff Quot).2 cont
  continuous_inv := by convert(@continuous_inv G _ _ _).quotient_map' _
#align topological_group_quotient topologicalGroup_quotient
#align topological_add_group_quotient topologicalAddGroup_quotient
-/

#print QuotientGroup.nhds_eq /-
/-- Neighborhoods in the quotient are precisely the map of neighborhoods in the prequotient. -/
@[to_additive
      "Neighborhoods in the quotient are precisely the map of neighborhoods in\nthe prequotient."]
theorem QuotientGroup.nhds_eq (x : G) : 𝓝 (x : G ⧸ N) = map coe (𝓝 x) :=
  le_antisymm ((QuotientGroup.isOpenMap_coe N).nhds_le x) continuous_quot_mk.ContinuousAt
#align quotient_group.nhds_eq QuotientGroup.nhds_eq
#align quotient_add_group.nhds_eq QuotientAddGroup.nhds_eq
-/

variable (G) [FirstCountableTopology G]

/- warning: topological_group.exists_antitone_basis_nhds_one -> TopologicalGroup.exists_antitone_basis_nhds_one is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] [_inst_4 : TopologicalSpace.FirstCountableTopology.{u1} G _inst_1], Exists.{succ u1} (Nat -> (Set.{u1} G)) (fun (u : Nat -> (Set.{u1} G)) => And (Filter.HasAntitoneBasis.{u1, 0} G Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))))) u) (forall (n : Nat), HasSubset.Subset.{u1} (Set.{u1} G) (Set.hasSubset.{u1} G) (HMul.hMul.{u1, u1, u1} (Set.{u1} G) (Set.{u1} G) (Set.{u1} G) (instHMul.{u1} (Set.{u1} G) (Set.mul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))) (u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (u n)))
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] [_inst_4 : TopologicalSpace.FirstCountableTopology.{u1} G _inst_1], Exists.{succ u1} (Nat -> (Set.{u1} G)) (fun (u : Nat -> (Set.{u1} G)) => And (Filter.HasAntitoneBasis.{u1, 0} G Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2))))))) u) (forall (n : Nat), HasSubset.Subset.{u1} (Set.{u1} G) (Set.instHasSubsetSet.{u1} G) (HMul.hMul.{u1, u1, u1} (Set.{u1} G) (Set.{u1} G) (Set.{u1} G) (instHMul.{u1} (Set.{u1} G) (Set.mul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))) (u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (u n)))
Case conversion may be inaccurate. Consider using '#align topological_group.exists_antitone_basis_nhds_one TopologicalGroup.exists_antitone_basis_nhds_oneₓ'. -/
/-- Any first countable topological group has an antitone neighborhood basis `u : ℕ → set G` for
which `(u (n + 1)) ^ 2 ⊆ u n`. The existence of such a neighborhood basis is a key tool for
`quotient_group.complete_space` -/
@[to_additive
      "Any first countable topological additive group has an antitone neighborhood basis\n`u : ℕ → set G` for which `u (n + 1) + u (n + 1) ⊆ u n`. The existence of such a neighborhood basis\nis a key tool for `quotient_add_group.complete_space`"]
theorem TopologicalGroup.exists_antitone_basis_nhds_one :
    ∃ u : ℕ → Set G, (𝓝 1).HasAntitoneBasis u ∧ ∀ n, u (n + 1) * u (n + 1) ⊆ u n :=
  by
  rcases(𝓝 (1 : G)).exists_antitone_basis with ⟨u, hu, u_anti⟩
  have :=
    ((hu.prod_nhds hu).tendsto_iffₓ hu).mp
      (by simpa only [mul_one] using continuous_mul.tendsto ((1, 1) : G × G))
  simp only [and_self_iff, mem_prod, and_imp, Prod.forall, exists_true_left, Prod.exists,
    forall_true_left] at this
  have event_mul : ∀ n : ℕ, ∀ᶠ m in at_top, u m * u m ⊆ u n :=
    by
    intro n
    rcases this n with ⟨j, k, h⟩
    refine' at_top_basis.eventually_iff.mpr ⟨max j k, True.intro, fun m hm => _⟩
    rintro - ⟨a, b, ha, hb, rfl⟩
    exact h a b (u_anti ((le_max_left _ _).trans hm) ha) (u_anti ((le_max_right _ _).trans hm) hb)
  obtain ⟨φ, -, hφ, φ_anti_basis⟩ := has_antitone_basis.subbasis_with_rel ⟨hu, u_anti⟩ event_mul
  exact ⟨u ∘ φ, φ_anti_basis, fun n => hφ n.lt_succ_self⟩
#align topological_group.exists_antitone_basis_nhds_one TopologicalGroup.exists_antitone_basis_nhds_one
#align topological_add_group.exists_antitone_basis_nhds_zero TopologicalAddGroup.exists_antitone_basis_nhds_zero

include n

/- warning: quotient_group.nhds_one_is_countably_generated -> QuotientGroup.nhds_one_isCountablyGenerated is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] (N : Subgroup.{u1} G _inst_2) (n : Subgroup.Normal.{u1} G _inst_2 N) [_inst_4 : TopologicalSpace.FirstCountableTopology.{u1} G _inst_1], Filter.IsCountablyGenerated.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_2) (QuotientGroup.Subgroup.hasQuotient.{u1} G _inst_2) N) (nhds.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_2) (QuotientGroup.Subgroup.hasQuotient.{u1} G _inst_2) N) (QuotientGroup.Quotient.topologicalSpace.{u1} G _inst_2 _inst_1 N) (OfNat.ofNat.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_2) (QuotientGroup.Subgroup.hasQuotient.{u1} G _inst_2) N) 1 (OfNat.mk.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_2) (QuotientGroup.Subgroup.hasQuotient.{u1} G _inst_2) N) 1 (One.one.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_2) (QuotientGroup.Subgroup.hasQuotient.{u1} G _inst_2) N) (MulOneClass.toHasOne.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_2) (QuotientGroup.Subgroup.hasQuotient.{u1} G _inst_2) N) (Monoid.toMulOneClass.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_2) (QuotientGroup.Subgroup.hasQuotient.{u1} G _inst_2) N) (DivInvMonoid.toMonoid.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_2) (QuotientGroup.Subgroup.hasQuotient.{u1} G _inst_2) N) (Group.toDivInvMonoid.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_2) (QuotientGroup.Subgroup.hasQuotient.{u1} G _inst_2) N) (QuotientGroup.Quotient.group.{u1} G _inst_2 N n)))))))))
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] (N : Subgroup.{u1} G _inst_2) (n : Subgroup.Normal.{u1} G _inst_2 N) [_inst_4 : TopologicalSpace.FirstCountableTopology.{u1} G _inst_1], Filter.IsCountablyGenerated.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_2) (QuotientGroup.instHasQuotientSubgroup.{u1} G _inst_2) N) (nhds.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_2) (QuotientGroup.instHasQuotientSubgroup.{u1} G _inst_2) N) (QuotientGroup.Quotient.topologicalSpace.{u1} G _inst_2 _inst_1 N) (OfNat.ofNat.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_2) (QuotientGroup.instHasQuotientSubgroup.{u1} G _inst_2) N) 1 (One.toOfNat1.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_2) (QuotientGroup.instHasQuotientSubgroup.{u1} G _inst_2) N) (InvOneClass.toOne.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_2) (QuotientGroup.instHasQuotientSubgroup.{u1} G _inst_2) N) (DivInvOneMonoid.toInvOneClass.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_2) (QuotientGroup.instHasQuotientSubgroup.{u1} G _inst_2) N) (DivisionMonoid.toDivInvOneMonoid.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_2) (QuotientGroup.instHasQuotientSubgroup.{u1} G _inst_2) N) (Group.toDivisionMonoid.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_2) (QuotientGroup.instHasQuotientSubgroup.{u1} G _inst_2) N) (QuotientGroup.Quotient.group.{u1} G _inst_2 N n))))))))
Case conversion may be inaccurate. Consider using '#align quotient_group.nhds_one_is_countably_generated QuotientGroup.nhds_one_isCountablyGeneratedₓ'. -/
/-- In a first countable topological group `G` with normal subgroup `N`, `1 : G ⧸ N` has a
countable neighborhood basis. -/
@[to_additive
      "In a first countable topological additive group `G` with normal additive subgroup\n`N`, `0 : G ⧸ N` has a countable neighborhood basis."]
instance QuotientGroup.nhds_one_isCountablyGenerated : (𝓝 (1 : G ⧸ N)).IsCountablyGenerated :=
  (QuotientGroup.nhds_eq N 1).symm ▸ map.isCountablyGenerated _ _
#align quotient_group.nhds_one_is_countably_generated QuotientGroup.nhds_one_isCountablyGenerated
#align quotient_add_group.nhds_zero_is_countably_generated QuotientAddGroup.nhds_zero_isCountablyGenerated

end QuotientTopologicalGroup

#print ContinuousSub /-
/-- A typeclass saying that `λ p : G × G, p.1 - p.2` is a continuous function. This property
automatically holds for topological additive groups but it also holds, e.g., for `ℝ≥0`. -/
class ContinuousSub (G : Type _) [TopologicalSpace G] [Sub G] : Prop where
  continuous_sub : Continuous fun p : G × G => p.1 - p.2
#align has_continuous_sub ContinuousSub
-/

#print ContinuousDiv /-
/-- A typeclass saying that `λ p : G × G, p.1 / p.2` is a continuous function. This property
automatically holds for topological groups. Lemmas using this class have primes.
The unprimed version is for `group_with_zero`. -/
@[to_additive]
class ContinuousDiv (G : Type _) [TopologicalSpace G] [Div G] : Prop where
  continuous_div' : Continuous fun p : G × G => p.1 / p.2
#align has_continuous_div ContinuousDiv
#align has_continuous_sub ContinuousSub
-/

/- warning: topological_group.to_has_continuous_div -> TopologicalGroup.to_continuousDiv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2], ContinuousDiv.{u1} G _inst_1 (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2], ContinuousDiv.{u1} G _inst_1 (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))
Case conversion may be inaccurate. Consider using '#align topological_group.to_has_continuous_div TopologicalGroup.to_continuousDivₓ'. -/
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) TopologicalGroup.to_continuousDiv [TopologicalSpace G] [Group G]
    [TopologicalGroup G] : ContinuousDiv G :=
  ⟨by
    simp only [div_eq_mul_inv]
    exact continuous_fst.mul continuous_snd.inv⟩
#align topological_group.to_has_continuous_div TopologicalGroup.to_continuousDiv
#align topological_add_group.to_has_continuous_sub TopologicalAddGroup.to_continuousSub

export ContinuousSub (continuous_sub)

export ContinuousDiv (continuous_div')

section ContinuousDiv

variable [TopologicalSpace G] [Div G] [ContinuousDiv G]

#print Filter.Tendsto.div' /-
@[to_additive sub]
theorem Filter.Tendsto.div' {f g : α → G} {l : Filter α} {a b : G} (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l (𝓝 b)) : Tendsto (fun x => f x / g x) l (𝓝 (a / b)) :=
  (continuous_div'.Tendsto (a, b)).comp (hf.prod_mk_nhds hg)
#align filter.tendsto.div' Filter.Tendsto.div'
#align filter.tendsto.sub Filter.Tendsto.sub
-/

#print Filter.Tendsto.const_div' /-
@[to_additive const_sub]
theorem Filter.Tendsto.const_div' (b : G) {c : G} {f : α → G} {l : Filter α}
    (h : Tendsto f l (𝓝 c)) : Tendsto (fun k : α => b / f k) l (𝓝 (b / c)) :=
  tendsto_const_nhds.div' h
#align filter.tendsto.const_div' Filter.Tendsto.const_div'
#align filter.tendsto.const_sub Filter.Tendsto.const_sub
-/

#print Filter.Tendsto.div_const' /-
@[to_additive sub_const]
theorem Filter.Tendsto.div_const' {c : G} {f : α → G} {l : Filter α} (h : Tendsto f l (𝓝 c))
    (b : G) : Tendsto (fun k : α => f k / b) l (𝓝 (c / b)) :=
  h.div' tendsto_const_nhds
#align filter.tendsto.div_const' Filter.Tendsto.div_const'
#align filter.tendsto.sub_const Filter.Tendsto.sub_const
-/

variable [TopologicalSpace α] {f g : α → G} {s : Set α} {x : α}

#print Continuous.div' /-
@[continuity, to_additive sub]
theorem Continuous.div' (hf : Continuous f) (hg : Continuous g) : Continuous fun x => f x / g x :=
  continuous_div'.comp (hf.prod_mk hg : _)
#align continuous.div' Continuous.div'
#align continuous.sub Continuous.sub
-/

#print continuous_div_left' /-
@[to_additive continuous_sub_left]
theorem continuous_div_left' (a : G) : Continuous fun b : G => a / b :=
  continuous_const.div' continuous_id
#align continuous_div_left' continuous_div_left'
#align continuous_sub_left continuous_sub_left
-/

#print continuous_div_right' /-
@[to_additive continuous_sub_right]
theorem continuous_div_right' (a : G) : Continuous fun b : G => b / a :=
  continuous_id.div' continuous_const
#align continuous_div_right' continuous_div_right'
#align continuous_sub_right continuous_sub_right
-/

#print ContinuousAt.div' /-
@[to_additive sub]
theorem ContinuousAt.div' {f g : α → G} {x : α} (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun x => f x / g x) x :=
  hf.div' hg
#align continuous_at.div' ContinuousAt.div'
#align continuous_at.sub ContinuousAt.sub
-/

#print ContinuousWithinAt.div' /-
@[to_additive sub]
theorem ContinuousWithinAt.div' (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x => f x / g x) s x :=
  hf.div' hg
#align continuous_within_at.div' ContinuousWithinAt.div'
#align continuous_within_at.sub ContinuousWithinAt.sub
-/

#print ContinuousOn.div' /-
@[to_additive sub]
theorem ContinuousOn.div' (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => f x / g x) s := fun x hx => (hf x hx).div' (hg x hx)
#align continuous_on.div' ContinuousOn.div'
#align continuous_on.sub ContinuousOn.sub
-/

end ContinuousDiv

section DivInTopologicalGroup

variable [Group G] [TopologicalSpace G] [TopologicalGroup G]

#print Homeomorph.divLeft /-
/-- A version of `homeomorph.mul_left a b⁻¹` that is defeq to `a / b`. -/
@[to_additive " A version of `homeomorph.add_left a (-b)` that is defeq to `a - b`. ",
  simps (config := { simpRhs := true })]
def Homeomorph.divLeft (x : G) : G ≃ₜ G :=
  { Equiv.divLeft x with
    continuous_toFun := continuous_const.div' continuous_id
    continuous_invFun := continuous_inv.mul continuous_const }
#align homeomorph.div_left Homeomorph.divLeft
#align homeomorph.sub_left Homeomorph.subLeft
-/

/- warning: is_open_map_div_left -> isOpenMap_div_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 _inst_1] (a : G), IsOpenMap.{u1, u1} G G _inst_2 _inst_2 (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 _inst_1] (a : G), IsOpenMap.{u1, u1} G G _inst_2 _inst_2 ((fun (x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.9546 : G) (x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.9548 : G) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.9546 x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.9548) a)
Case conversion may be inaccurate. Consider using '#align is_open_map_div_left isOpenMap_div_leftₓ'. -/
@[to_additive]
theorem isOpenMap_div_left (a : G) : IsOpenMap ((· / ·) a) :=
  (Homeomorph.divLeft _).IsOpenMap
#align is_open_map_div_left isOpenMap_div_left
#align is_open_map_sub_left isOpenMap_sub_left

/- warning: is_closed_map_div_left -> isClosedMap_div_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 _inst_1] (a : G), IsClosedMap.{u1, u1} G G _inst_2 _inst_2 (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 _inst_1] (a : G), IsClosedMap.{u1, u1} G G _inst_2 _inst_2 ((fun (x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.9588 : G) (x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.9590 : G) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.9588 x._@.Mathlib.Topology.Algebra.Group.Basic._hyg.9590) a)
Case conversion may be inaccurate. Consider using '#align is_closed_map_div_left isClosedMap_div_leftₓ'. -/
@[to_additive]
theorem isClosedMap_div_left (a : G) : IsClosedMap ((· / ·) a) :=
  (Homeomorph.divLeft _).IsClosedMap
#align is_closed_map_div_left isClosedMap_div_left
#align is_closed_map_sub_left isClosedMap_sub_left

#print Homeomorph.divRight /-
/-- A version of `homeomorph.mul_right a⁻¹ b` that is defeq to `b / a`. -/
@[to_additive " A version of `homeomorph.add_right (-a) b` that is defeq to `b - a`. ",
  simps (config := { simpRhs := true })]
def Homeomorph.divRight (x : G) : G ≃ₜ G :=
  { Equiv.divRight x with
    continuous_toFun := continuous_id.div' continuous_const
    continuous_invFun := continuous_id.mul continuous_const }
#align homeomorph.div_right Homeomorph.divRight
#align homeomorph.sub_right Homeomorph.subRight
-/

/- warning: is_open_map_div_right -> isOpenMap_div_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 _inst_1] (a : G), IsOpenMap.{u1, u1} G G _inst_2 _inst_2 (fun (x : G) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) x a)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 _inst_1] (a : G), IsOpenMap.{u1, u1} G G _inst_2 _inst_2 (fun (x : G) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) x a)
Case conversion may be inaccurate. Consider using '#align is_open_map_div_right isOpenMap_div_rightₓ'. -/
@[to_additive]
theorem isOpenMap_div_right (a : G) : IsOpenMap fun x => x / a :=
  (Homeomorph.divRight a).IsOpenMap
#align is_open_map_div_right isOpenMap_div_right
#align is_open_map_sub_right isOpenMap_sub_right

/- warning: is_closed_map_div_right -> isClosedMap_div_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 _inst_1] (a : G), IsClosedMap.{u1, u1} G G _inst_2 _inst_2 (fun (x : G) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) x a)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 _inst_1] (a : G), IsClosedMap.{u1, u1} G G _inst_2 _inst_2 (fun (x : G) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) x a)
Case conversion may be inaccurate. Consider using '#align is_closed_map_div_right isClosedMap_div_rightₓ'. -/
@[to_additive]
theorem isClosedMap_div_right (a : G) : IsClosedMap fun x => x / a :=
  (Homeomorph.divRight a).IsClosedMap
#align is_closed_map_div_right isClosedMap_div_right
#align is_closed_map_sub_right isClosedMap_sub_right

/- warning: tendsto_div_nhds_one_iff -> tendsto_div_nhds_one_iff is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 _inst_1] {α : Type.{u2}} {l : Filter.{u2} α} {x : G} {u : α -> G}, Iff (Filter.Tendsto.{u2, u1} α G (fun (n : α) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (u n) x) l (nhds.{u1} G _inst_2 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))))) (Filter.Tendsto.{u2, u1} α G u l (nhds.{u1} G _inst_2 x))
but is expected to have type
  forall {G : Type.{u2}} [_inst_1 : Group.{u2} G] [_inst_2 : TopologicalSpace.{u2} G] [_inst_3 : TopologicalGroup.{u2} G _inst_2 _inst_1] {α : Type.{u1}} {l : Filter.{u1} α} {x : G} {u : α -> G}, Iff (Filter.Tendsto.{u1, u2} α G (fun (n : α) => HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G (DivInvMonoid.toDiv.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (u n) x) l (nhds.{u2} G _inst_2 (OfNat.ofNat.{u2} G 1 (One.toOfNat1.{u2} G (InvOneClass.toOne.{u2} G (DivInvOneMonoid.toInvOneClass.{u2} G (DivisionMonoid.toDivInvOneMonoid.{u2} G (Group.toDivisionMonoid.{u2} G _inst_1)))))))) (Filter.Tendsto.{u1, u2} α G u l (nhds.{u2} G _inst_2 x))
Case conversion may be inaccurate. Consider using '#align tendsto_div_nhds_one_iff tendsto_div_nhds_one_iffₓ'. -/
@[to_additive]
theorem tendsto_div_nhds_one_iff {α : Type _} {l : Filter α} {x : G} {u : α → G} :
    Tendsto (fun n => u n / x) l (𝓝 1) ↔ Tendsto u l (𝓝 x) :=
  haveI A : tendsto (fun n : α => x) l (𝓝 x) := tendsto_const_nhds
  ⟨fun h => by simpa using h.mul A, fun h => by simpa using h.div' A⟩
#align tendsto_div_nhds_one_iff tendsto_div_nhds_one_iff
#align tendsto_sub_nhds_zero_iff tendsto_sub_nhds_zero_iff

/- warning: nhds_translation_div -> nhds_translation_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 _inst_1] (x : G), Eq.{succ u1} (Filter.{u1} G) (Filter.comap.{u1, u1} G G (fun (_x : G) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) _x x) (nhds.{u1} G _inst_2 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))))) (nhds.{u1} G _inst_2 x)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_2 _inst_1] (x : G), Eq.{succ u1} (Filter.{u1} G) (Filter.comap.{u1, u1} G G (fun (_x : G) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) _x x) (nhds.{u1} G _inst_2 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))))))) (nhds.{u1} G _inst_2 x)
Case conversion may be inaccurate. Consider using '#align nhds_translation_div nhds_translation_divₓ'. -/
@[to_additive]
theorem nhds_translation_div (x : G) : comap (· / x) (𝓝 1) = 𝓝 x := by
  simpa only [div_eq_mul_inv] using nhds_translation_mul_inv x
#align nhds_translation_div nhds_translation_div
#align nhds_translation_sub nhds_translation_sub

end DivInTopologicalGroup

/-!
### Topological operations on pointwise sums and products

A few results about interior and closure of the pointwise addition/multiplication of sets in groups
with continuous addition/multiplication. See also `submonoid.top_closure_mul_self_eq` in
`topology.algebra.monoid`.
-/


section ContinuousConstSMul

variable [TopologicalSpace β] [Group α] [MulAction α β] [ContinuousConstSMul α β] {s : Set α}
  {t : Set β}

#print IsOpen.smul_left /-
@[to_additive]
theorem IsOpen.smul_left (ht : IsOpen t) : IsOpen (s • t) :=
  by
  rw [← bUnion_smul_set]
  exact isOpen_bunionᵢ fun a _ => ht.smul _
#align is_open.smul_left IsOpen.smul_left
#align is_open.vadd_left IsOpen.vadd_left
-/

#print subset_interior_smul_right /-
@[to_additive]
theorem subset_interior_smul_right : s • interior t ⊆ interior (s • t) :=
  interior_maximal (Set.smul_subset_smul_left interior_subset) isOpen_interior.smul_left
#align subset_interior_smul_right subset_interior_smul_right
#align subset_interior_vadd_right subset_interior_vadd_right
-/

#print smul_mem_nhds /-
@[to_additive]
theorem smul_mem_nhds (a : α) {x : β} (ht : t ∈ 𝓝 x) : a • t ∈ 𝓝 (a • x) :=
  by
  rcases mem_nhds_iff.1 ht with ⟨u, ut, u_open, hu⟩
  exact mem_nhds_iff.2 ⟨a • u, smul_set_mono ut, u_open.smul a, smul_mem_smul_set hu⟩
#align smul_mem_nhds smul_mem_nhds
#align vadd_mem_nhds vadd_mem_nhds
-/

variable [TopologicalSpace α]

#print subset_interior_smul /-
@[to_additive]
theorem subset_interior_smul : interior s • interior t ⊆ interior (s • t) :=
  (Set.smul_subset_smul_right interior_subset).trans subset_interior_smul_right
#align subset_interior_smul subset_interior_smul
#align subset_interior_vadd subset_interior_vadd
-/

end ContinuousConstSMul

section ContinuousConstSMul

variable [TopologicalSpace α] [Group α] [ContinuousConstSMul α α] {s t : Set α}

/- warning: is_open.mul_left -> IsOpen.mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : ContinuousConstSMul.{u1, u1} α α _inst_1 (Mul.toSMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))] {s : Set.{u1} α} {t : Set.{u1} α}, (IsOpen.{u1} α _inst_1 t) -> (IsOpen.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : ContinuousConstSMul.{u1, u1} α α _inst_1 (MulAction.toSMul.{u1, u1} α α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) (Monoid.toMulAction.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))] {s : Set.{u1} α} {t : Set.{u1} α}, (IsOpen.{u1} α _inst_1 t) -> (IsOpen.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) s t))
Case conversion may be inaccurate. Consider using '#align is_open.mul_left IsOpen.mul_leftₓ'. -/
@[to_additive]
theorem IsOpen.mul_left : IsOpen t → IsOpen (s * t) :=
  IsOpen.smul_left
#align is_open.mul_left IsOpen.mul_left
#align is_open.add_left IsOpen.add_left

/- warning: subset_interior_mul_right -> subset_interior_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : ContinuousConstSMul.{u1, u1} α α _inst_1 (Mul.toSMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))] {s : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) s (interior.{u1} α _inst_1 t)) (interior.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : ContinuousConstSMul.{u1, u1} α α _inst_1 (MulAction.toSMul.{u1, u1} α α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) (Monoid.toMulAction.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))] {s : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) s (interior.{u1} α _inst_1 t)) (interior.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) s t))
Case conversion may be inaccurate. Consider using '#align subset_interior_mul_right subset_interior_mul_rightₓ'. -/
@[to_additive]
theorem subset_interior_mul_right : s * interior t ⊆ interior (s * t) :=
  subset_interior_smul_right
#align subset_interior_mul_right subset_interior_mul_right
#align subset_interior_add_right subset_interior_add_right

/- warning: subset_interior_mul -> subset_interior_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : ContinuousConstSMul.{u1, u1} α α _inst_1 (Mul.toSMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))] {s : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) (interior.{u1} α _inst_1 s) (interior.{u1} α _inst_1 t)) (interior.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : ContinuousConstSMul.{u1, u1} α α _inst_1 (MulAction.toSMul.{u1, u1} α α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) (Monoid.toMulAction.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))] {s : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) (interior.{u1} α _inst_1 s) (interior.{u1} α _inst_1 t)) (interior.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) s t))
Case conversion may be inaccurate. Consider using '#align subset_interior_mul subset_interior_mulₓ'. -/
@[to_additive]
theorem subset_interior_mul : interior s * interior t ⊆ interior (s * t) :=
  subset_interior_smul
#align subset_interior_mul subset_interior_mul
#align subset_interior_add subset_interior_add

/- warning: singleton_mul_mem_nhds -> singleton_mul_mem_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : ContinuousConstSMul.{u1, u1} α α _inst_1 (Mul.toSMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))] {s : Set.{u1} α} (a : α) {b : α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α _inst_1 b)) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a) s) (nhds.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : ContinuousConstSMul.{u1, u1} α α _inst_1 (MulAction.toSMul.{u1, u1} α α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) (Monoid.toMulAction.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))] {s : Set.{u1} α} (a : α) {b : α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (nhds.{u1} α _inst_1 b)) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a) s) (nhds.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) a b)))
Case conversion may be inaccurate. Consider using '#align singleton_mul_mem_nhds singleton_mul_mem_nhdsₓ'. -/
@[to_additive]
theorem singleton_mul_mem_nhds (a : α) {b : α} (h : s ∈ 𝓝 b) : {a} * s ∈ 𝓝 (a * b) :=
  by
  have := smul_mem_nhds a h
  rwa [← singleton_smul] at this
#align singleton_mul_mem_nhds singleton_mul_mem_nhds
#align singleton_add_mem_nhds singleton_add_mem_nhds

/- warning: singleton_mul_mem_nhds_of_nhds_one -> singleton_mul_mem_nhds_of_nhds_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : ContinuousConstSMul.{u1, u1} α α _inst_1 (Mul.toSMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))] {s : Set.{u1} α} (a : α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))))))) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a) s) (nhds.{u1} α _inst_1 a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : ContinuousConstSMul.{u1, u1} α α _inst_1 (MulAction.toSMul.{u1, u1} α α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) (Monoid.toMulAction.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))] {s : Set.{u1} α} (a : α), (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (nhds.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2)))))))) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a) s) (nhds.{u1} α _inst_1 a))
Case conversion may be inaccurate. Consider using '#align singleton_mul_mem_nhds_of_nhds_one singleton_mul_mem_nhds_of_nhds_oneₓ'. -/
@[to_additive]
theorem singleton_mul_mem_nhds_of_nhds_one (a : α) (h : s ∈ 𝓝 (1 : α)) : {a} * s ∈ 𝓝 a := by
  simpa only [mul_one] using singleton_mul_mem_nhds a h
#align singleton_mul_mem_nhds_of_nhds_one singleton_mul_mem_nhds_of_nhds_one
#align singleton_add_mem_nhds_of_nhds_zero singleton_add_mem_nhds_of_nhds_zero

end ContinuousConstSMul

section HasContinuousConstSmulOp

variable [TopologicalSpace α] [Group α] [ContinuousConstSMul αᵐᵒᵖ α] {s t : Set α}

/- warning: is_open.mul_right -> IsOpen.mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : ContinuousConstSMul.{u1, u1} (MulOpposite.{u1} α) α _inst_1 (Mul.toHasOppositeSMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))] {s : Set.{u1} α} {t : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (IsOpen.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : ContinuousConstSMul.{u1, u1} (MulOpposite.{u1} α) α _inst_1 (Mul.toHasOppositeSMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))] {s : Set.{u1} α} {t : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (IsOpen.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) s t))
Case conversion may be inaccurate. Consider using '#align is_open.mul_right IsOpen.mul_rightₓ'. -/
@[to_additive]
theorem IsOpen.mul_right (hs : IsOpen s) : IsOpen (s * t) :=
  by
  rw [← bUnion_op_smul_set]
  exact isOpen_bunionᵢ fun a _ => hs.smul _
#align is_open.mul_right IsOpen.mul_right
#align is_open.add_right IsOpen.add_right

/- warning: subset_interior_mul_left -> subset_interior_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : ContinuousConstSMul.{u1, u1} (MulOpposite.{u1} α) α _inst_1 (Mul.toHasOppositeSMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))] {s : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) (interior.{u1} α _inst_1 s) t) (interior.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : ContinuousConstSMul.{u1, u1} (MulOpposite.{u1} α) α _inst_1 (Mul.toHasOppositeSMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))] {s : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) (interior.{u1} α _inst_1 s) t) (interior.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) s t))
Case conversion may be inaccurate. Consider using '#align subset_interior_mul_left subset_interior_mul_leftₓ'. -/
@[to_additive]
theorem subset_interior_mul_left : interior s * t ⊆ interior (s * t) :=
  interior_maximal (Set.mul_subset_mul_right interior_subset) isOpen_interior.mulRight
#align subset_interior_mul_left subset_interior_mul_left
#align subset_interior_add_left subset_interior_add_left

/- warning: subset_interior_mul' -> subset_interior_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : ContinuousConstSMul.{u1, u1} (MulOpposite.{u1} α) α _inst_1 (Mul.toHasOppositeSMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))] {s : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) (interior.{u1} α _inst_1 s) (interior.{u1} α _inst_1 t)) (interior.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : ContinuousConstSMul.{u1, u1} (MulOpposite.{u1} α) α _inst_1 (Mul.toHasOppositeSMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))] {s : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) (interior.{u1} α _inst_1 s) (interior.{u1} α _inst_1 t)) (interior.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) s t))
Case conversion may be inaccurate. Consider using '#align subset_interior_mul' subset_interior_mul'ₓ'. -/
@[to_additive]
theorem subset_interior_mul' : interior s * interior t ⊆ interior (s * t) :=
  (Set.mul_subset_mul_left interior_subset).trans subset_interior_mul_left
#align subset_interior_mul' subset_interior_mul'
#align subset_interior_add' subset_interior_add'

/- warning: mul_singleton_mem_nhds -> mul_singleton_mem_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : ContinuousConstSMul.{u1, u1} (MulOpposite.{u1} α) α _inst_1 (Mul.toHasOppositeSMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))] {s : Set.{u1} α} (a : α) {b : α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α _inst_1 b)) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)) (nhds.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) b a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : ContinuousConstSMul.{u1, u1} (MulOpposite.{u1} α) α _inst_1 (Mul.toHasOppositeSMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))] {s : Set.{u1} α} (a : α) {b : α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (nhds.{u1} α _inst_1 b)) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)) (nhds.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))) b a)))
Case conversion may be inaccurate. Consider using '#align mul_singleton_mem_nhds mul_singleton_mem_nhdsₓ'. -/
@[to_additive]
theorem mul_singleton_mem_nhds (a : α) {b : α} (h : s ∈ 𝓝 b) : s * {a} ∈ 𝓝 (b * a) :=
  by
  simp only [← bUnion_op_smul_set, mem_singleton_iff, Union_Union_eq_left]
  exact smul_mem_nhds _ h
#align mul_singleton_mem_nhds mul_singleton_mem_nhds
#align add_singleton_mem_nhds add_singleton_mem_nhds

/- warning: mul_singleton_mem_nhds_of_nhds_one -> mul_singleton_mem_nhds_of_nhds_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : ContinuousConstSMul.{u1, u1} (MulOpposite.{u1} α) α _inst_1 (Mul.toHasOppositeSMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))] {s : Set.{u1} α} (a : α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))))))) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)) (nhds.{u1} α _inst_1 a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : ContinuousConstSMul.{u1, u1} (MulOpposite.{u1} α) α _inst_1 (Mul.toHasOppositeSMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))] {s : Set.{u1} α} (a : α), (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (nhds.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2)))))))) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)) (nhds.{u1} α _inst_1 a))
Case conversion may be inaccurate. Consider using '#align mul_singleton_mem_nhds_of_nhds_one mul_singleton_mem_nhds_of_nhds_oneₓ'. -/
@[to_additive]
theorem mul_singleton_mem_nhds_of_nhds_one (a : α) (h : s ∈ 𝓝 (1 : α)) : s * {a} ∈ 𝓝 a := by
  simpa only [one_mul] using mul_singleton_mem_nhds a h
#align mul_singleton_mem_nhds_of_nhds_one mul_singleton_mem_nhds_of_nhds_one
#align add_singleton_mem_nhds_of_nhds_zero add_singleton_mem_nhds_of_nhds_zero

end HasContinuousConstSmulOp

section TopologicalGroup

variable [TopologicalSpace α] [Group α] [TopologicalGroup α] {s t : Set α}

/- warning: is_open.div_left -> IsOpen.div_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : TopologicalGroup.{u1} α _inst_1 _inst_2] {s : Set.{u1} α} {t : Set.{u1} α}, (IsOpen.{u1} α _inst_1 t) -> (IsOpen.{u1} α _inst_1 (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : TopologicalGroup.{u1} α _inst_1 _inst_2] {s : Set.{u1} α} {t : Set.{u1} α}, (IsOpen.{u1} α _inst_1 t) -> (IsOpen.{u1} α _inst_1 (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) s t))
Case conversion may be inaccurate. Consider using '#align is_open.div_left IsOpen.div_leftₓ'. -/
@[to_additive]
theorem IsOpen.div_left (ht : IsOpen t) : IsOpen (s / t) :=
  by
  rw [← Union_div_left_image]
  exact isOpen_bunionᵢ fun a ha => isOpenMap_div_left a t ht
#align is_open.div_left IsOpen.div_left
#align is_open.sub_left IsOpen.sub_left

/- warning: is_open.div_right -> IsOpen.div_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : TopologicalGroup.{u1} α _inst_1 _inst_2] {s : Set.{u1} α} {t : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (IsOpen.{u1} α _inst_1 (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : TopologicalGroup.{u1} α _inst_1 _inst_2] {s : Set.{u1} α} {t : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (IsOpen.{u1} α _inst_1 (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) s t))
Case conversion may be inaccurate. Consider using '#align is_open.div_right IsOpen.div_rightₓ'. -/
@[to_additive]
theorem IsOpen.div_right (hs : IsOpen s) : IsOpen (s / t) :=
  by
  rw [← Union_div_right_image]
  exact isOpen_bunionᵢ fun a ha => isOpenMap_div_right a s hs
#align is_open.div_right IsOpen.div_right
#align is_open.sub_right IsOpen.sub_right

/- warning: subset_interior_div_left -> subset_interior_div_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : TopologicalGroup.{u1} α _inst_1 _inst_2] {s : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) (interior.{u1} α _inst_1 s) t) (interior.{u1} α _inst_1 (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : TopologicalGroup.{u1} α _inst_1 _inst_2] {s : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) (interior.{u1} α _inst_1 s) t) (interior.{u1} α _inst_1 (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) s t))
Case conversion may be inaccurate. Consider using '#align subset_interior_div_left subset_interior_div_leftₓ'. -/
@[to_additive]
theorem subset_interior_div_left : interior s / t ⊆ interior (s / t) :=
  interior_maximal (div_subset_div_right interior_subset) isOpen_interior.divRight
#align subset_interior_div_left subset_interior_div_left
#align subset_interior_sub_left subset_interior_sub_left

/- warning: subset_interior_div_right -> subset_interior_div_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : TopologicalGroup.{u1} α _inst_1 _inst_2] {s : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) s (interior.{u1} α _inst_1 t)) (interior.{u1} α _inst_1 (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : TopologicalGroup.{u1} α _inst_1 _inst_2] {s : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) s (interior.{u1} α _inst_1 t)) (interior.{u1} α _inst_1 (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) s t))
Case conversion may be inaccurate. Consider using '#align subset_interior_div_right subset_interior_div_rightₓ'. -/
@[to_additive]
theorem subset_interior_div_right : s / interior t ⊆ interior (s / t) :=
  interior_maximal (div_subset_div_left interior_subset) isOpen_interior.divLeft
#align subset_interior_div_right subset_interior_div_right
#align subset_interior_sub_right subset_interior_sub_right

/- warning: subset_interior_div -> subset_interior_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : TopologicalGroup.{u1} α _inst_1 _inst_2] {s : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) (interior.{u1} α _inst_1 s) (interior.{u1} α _inst_1 t)) (interior.{u1} α _inst_1 (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : TopologicalGroup.{u1} α _inst_1 _inst_2] {s : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) (interior.{u1} α _inst_1 s) (interior.{u1} α _inst_1 t)) (interior.{u1} α _inst_1 (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) s t))
Case conversion may be inaccurate. Consider using '#align subset_interior_div subset_interior_divₓ'. -/
@[to_additive]
theorem subset_interior_div : interior s / interior t ⊆ interior (s / t) :=
  (div_subset_div_left interior_subset).trans subset_interior_div_left
#align subset_interior_div subset_interior_div
#align subset_interior_sub subset_interior_sub

/- warning: is_open.mul_closure -> IsOpen.mul_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : TopologicalGroup.{u1} α _inst_1 _inst_2] {s : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (forall (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) s (closure.{u1} α _inst_1 t)) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : TopologicalGroup.{u1} α _inst_1 _inst_2] {s : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (forall (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) s (closure.{u1} α _inst_1 t)) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) s t))
Case conversion may be inaccurate. Consider using '#align is_open.mul_closure IsOpen.mul_closureₓ'. -/
@[to_additive]
theorem IsOpen.mul_closure (hs : IsOpen s) (t : Set α) : s * closure t = s * t :=
  by
  refine' (mul_subset_iff.2 fun a ha b hb => _).antisymm (mul_subset_mul_left subset_closure)
  rw [mem_closure_iff] at hb
  have hbU : b ∈ s⁻¹ * {a * b} := ⟨a⁻¹, a * b, Set.inv_mem_inv.2 ha, rfl, inv_mul_cancel_left _ _⟩
  obtain ⟨_, ⟨c, d, hc, rfl : d = _, rfl⟩, hcs⟩ := hb _ hs.inv.mul_right hbU
  exact ⟨c⁻¹, _, hc, hcs, inv_mul_cancel_left _ _⟩
#align is_open.mul_closure IsOpen.mul_closure
#align is_open.add_closure IsOpen.add_closure

/- warning: is_open.closure_mul -> IsOpen.closure_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : TopologicalGroup.{u1} α _inst_1 _inst_2] {t : Set.{u1} α}, (IsOpen.{u1} α _inst_1 t) -> (forall (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) (closure.{u1} α _inst_1 s) t) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : TopologicalGroup.{u1} α _inst_1 _inst_2] {t : Set.{u1} α}, (IsOpen.{u1} α _inst_1 t) -> (forall (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) (closure.{u1} α _inst_1 s) t) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) s t))
Case conversion may be inaccurate. Consider using '#align is_open.closure_mul IsOpen.closure_mulₓ'. -/
@[to_additive]
theorem IsOpen.closure_mul (ht : IsOpen t) (s : Set α) : closure s * t = s * t := by
  rw [← inv_inv (closure s * t), mul_inv_rev, inv_closure, ht.inv.mul_closure, mul_inv_rev, inv_inv,
    inv_inv]
#align is_open.closure_mul IsOpen.closure_mul
#align is_open.closure_add IsOpen.closure_add

/- warning: is_open.div_closure -> IsOpen.div_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : TopologicalGroup.{u1} α _inst_1 _inst_2] {s : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (forall (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) s (closure.{u1} α _inst_1 t)) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : TopologicalGroup.{u1} α _inst_1 _inst_2] {s : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (forall (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) s (closure.{u1} α _inst_1 t)) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) s t))
Case conversion may be inaccurate. Consider using '#align is_open.div_closure IsOpen.div_closureₓ'. -/
@[to_additive]
theorem IsOpen.div_closure (hs : IsOpen s) (t : Set α) : s / closure t = s / t := by
  simp_rw [div_eq_mul_inv, inv_closure, hs.mul_closure]
#align is_open.div_closure IsOpen.div_closure
#align is_open.sub_closure IsOpen.sub_closure

/- warning: is_open.closure_div -> IsOpen.closure_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : TopologicalGroup.{u1} α _inst_1 _inst_2] {t : Set.{u1} α}, (IsOpen.{u1} α _inst_1 t) -> (forall (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) (closure.{u1} α _inst_1 s) t) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u1} α] [_inst_3 : TopologicalGroup.{u1} α _inst_1 _inst_2] {t : Set.{u1} α}, (IsOpen.{u1} α _inst_1 t) -> (forall (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) (closure.{u1} α _inst_1 s) t) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))) s t))
Case conversion may be inaccurate. Consider using '#align is_open.closure_div IsOpen.closure_divₓ'. -/
@[to_additive]
theorem IsOpen.closure_div (ht : IsOpen t) (s : Set α) : closure s / t = s / t := by
  simp_rw [div_eq_mul_inv, ht.inv.closure_mul]
#align is_open.closure_div IsOpen.closure_div
#align is_open.closure_sub IsOpen.closure_sub

end TopologicalGroup

#print AddGroupWithZeroNhd /-
/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`z] [] -/
/-- additive group with a neighbourhood around 0.
Only used to construct a topology and uniform space.

This is currently only available for commutative groups, but it can be extended to
non-commutative groups too.
-/
class AddGroupWithZeroNhd (G : Type u) extends AddCommGroup G where
  z : Filter G
  zero_z : pure 0 ≤ Z
  sub_z : Tendsto (fun p : G × G => p.1 - p.2) (Z ×ᶠ Z) Z
#align add_group_with_zero_nhd AddGroupWithZeroNhd
-/

section FilterMul

section

variable (G) [TopologicalSpace G] [Group G] [ContinuousMul G]

/- warning: topological_group.t1_space -> TopologicalGroup.t1Space is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))], (IsClosed.{u1} G _inst_1 (Singleton.singleton.{u1, u1} G (Set.{u1} G) (Set.hasSingleton.{u1} G) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))))))) -> (T1Space.{u1} G _inst_1)
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))], (IsClosed.{u1} G _inst_1 (Singleton.singleton.{u1, u1} G (Set.{u1} G) (Set.instSingletonSet.{u1} G) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))))))) -> (T1Space.{u1} G _inst_1)
Case conversion may be inaccurate. Consider using '#align topological_group.t1_space TopologicalGroup.t1Spaceₓ'. -/
@[to_additive]
theorem TopologicalGroup.t1Space (h : @IsClosed G _ {1}) : T1Space G :=
  ⟨fun x => by
    convert isClosedMap_mul_right x _ h
    simp⟩
#align topological_group.t1_space TopologicalGroup.t1Space
#align topological_add_group.t1_space TopologicalAddGroup.t1Space

end

section

variable (G) [TopologicalSpace G] [Group G] [TopologicalGroup G]

#print TopologicalGroup.regularSpace /-
@[to_additive]
instance (priority := 100) TopologicalGroup.regularSpace : RegularSpace G :=
  by
  refine' RegularSpace.ofExistsMemNhdsIsClosedSubset fun a s hs => _
  have : tendsto (fun p : G × G => p.1 * p.2) (𝓝 (a, 1)) (𝓝 a) :=
    continuous_mul.tendsto' _ _ (mul_one a)
  rcases mem_nhds_prod_iff.mp (this hs) with ⟨U, hU, V, hV, hUV⟩
  rw [← image_subset_iff, image_prod] at hUV
  refine' ⟨closure U, mem_of_superset hU subset_closure, isClosed_closure, _⟩
  calc
    closure U ⊆ closure U * interior V := subset_mul_left _ (mem_interior_iff_mem_nhds.2 hV)
    _ = U * interior V := (is_open_interior.closure_mul U)
    _ ⊆ U * V := (mul_subset_mul_left interior_subset)
    _ ⊆ s := hUV
    
#align topological_group.regular_space TopologicalGroup.regularSpace
#align topological_add_group.regular_space TopologicalAddGroup.regularSpace
-/

#print TopologicalGroup.t3Space /-
@[to_additive]
theorem TopologicalGroup.t3Space [T0Space G] : T3Space G :=
  ⟨⟩
#align topological_group.t3_space TopologicalGroup.t3Space
#align topological_add_group.t3_space TopologicalAddGroup.t3Space
-/

#print TopologicalGroup.t2Space /-
@[to_additive]
theorem TopologicalGroup.t2Space [T0Space G] : T2Space G :=
  by
  haveI := TopologicalGroup.t3Space G
  infer_instance
#align topological_group.t2_space TopologicalGroup.t2Space
#align topological_add_group.t2_space TopologicalAddGroup.t2Space
-/

variable {G} (S : Subgroup G) [Subgroup.Normal S] [IsClosed (S : Set G)]

/- warning: subgroup.t3_quotient_of_is_closed -> Subgroup.t3_quotient_of_isClosed is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] (S : Subgroup.{u1} G _inst_2) [_inst_6 : Subgroup.Normal.{u1} G _inst_2 S] [hS : IsClosed.{u1} G _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subgroup.{u1} G _inst_2) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)))) S)], T3Space.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_2) (QuotientGroup.Subgroup.hasQuotient.{u1} G _inst_2) S) (QuotientGroup.Quotient.topologicalSpace.{u1} G _inst_2 _inst_1 S)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] (S : Subgroup.{u1} G _inst_2) [_inst_6 : Subgroup.Normal.{u1} G _inst_2 S] [hS : IsClosed.{u1} G _inst_1 (SetLike.coe.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2) S)], T3Space.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_2) (QuotientGroup.instHasQuotientSubgroup.{u1} G _inst_2) S) (QuotientGroup.Quotient.topologicalSpace.{u1} G _inst_2 _inst_1 S)
Case conversion may be inaccurate. Consider using '#align subgroup.t3_quotient_of_is_closed Subgroup.t3_quotient_of_isClosedₓ'. -/
@[to_additive]
instance Subgroup.t3_quotient_of_isClosed (S : Subgroup G) [Subgroup.Normal S]
    [hS : IsClosed (S : Set G)] : T3Space (G ⧸ S) :=
  by
  rw [← QuotientGroup.ker_mk' S] at hS
  haveI := TopologicalGroup.t1Space (G ⧸ S) (quotient_map_quotient_mk.is_closed_preimage.mp hS)
  exact TopologicalGroup.t3Space _
#align subgroup.t3_quotient_of_is_closed Subgroup.t3_quotient_of_isClosed
#align add_subgroup.t3_quotient_of_is_closed AddSubgroup.t3_quotient_of_isClosed

/- warning: subgroup.properly_discontinuous_smul_of_tendsto_cofinite -> Subgroup.properlyDiscontinuousSMul_of_tendsto_cofinite is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] (S : Subgroup.{u1} G _inst_2), (Filter.Tendsto.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) G (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) G (Monoid.toMulOneClass.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) (Subgroup.toGroup.{u1} G _inst_2 S)))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) (fun (_x : MonoidHom.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) G (Monoid.toMulOneClass.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) (Subgroup.toGroup.{u1} G _inst_2 S)))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) => (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) -> G) (MonoidHom.hasCoeToFun.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) G (Monoid.toMulOneClass.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) (Subgroup.toGroup.{u1} G _inst_2 S)))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) (Subgroup.subtype.{u1} G _inst_2 S)) (Filter.cofinite.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S)) (Filter.cocompact.{u1} G _inst_1)) -> (ProperlyDiscontinuousSMul.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) G _inst_1 (MulAction.toHasSmul.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) G (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) (Subgroup.toGroup.{u1} G _inst_2 S))) (Subgroup.mulAction.{u1, u1} G _inst_2 G (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) S)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] (S : Subgroup.{u1} G _inst_2), (Filter.Tendsto.{u1, u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x S)) G (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x S)) G (Submonoid.toMulOneClass.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Subgroup.toSubmonoid.{u1} G _inst_2 S)) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x S)) (fun (_x : Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x S)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x S)) => G) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x S)) G (Submonoid.toMulOneClass.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Subgroup.toSubmonoid.{u1} G _inst_2 S)) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x S)) G (MulOneClass.toMul.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x S)) (Submonoid.toMulOneClass.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Subgroup.toSubmonoid.{u1} G _inst_2 S))) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x S)) G (Submonoid.toMulOneClass.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Subgroup.toSubmonoid.{u1} G _inst_2 S)) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x S)) G (Submonoid.toMulOneClass.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Subgroup.toSubmonoid.{u1} G _inst_2 S)) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (MonoidHom.monoidHomClass.{u1, u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x S)) G (Submonoid.toMulOneClass.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Subgroup.toSubmonoid.{u1} G _inst_2 S)) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))) (Subgroup.subtype.{u1} G _inst_2 S)) (Filter.cofinite.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x S))) (Filter.cocompact.{u1} G _inst_1)) -> (ProperlyDiscontinuousSMul.{u1, u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x S)) G _inst_1 (Submonoid.smul.{u1, u1} G G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (MulAction.toSMul.{u1, u1} G G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) (Subgroup.toSubmonoid.{u1} G _inst_2 S)))
Case conversion may be inaccurate. Consider using '#align subgroup.properly_discontinuous_smul_of_tendsto_cofinite Subgroup.properlyDiscontinuousSMul_of_tendsto_cofiniteₓ'. -/
/-- A subgroup `S` of a topological group `G` acts on `G` properly discontinuously on the left, if
it is discrete in the sense that `S ∩ K` is finite for all compact `K`. (See also
`discrete_topology`.) -/
@[to_additive
      "A subgroup `S` of an additive topological group `G` acts on `G` properly\ndiscontinuously on the left, if it is discrete in the sense that `S ∩ K` is finite for all compact\n`K`. (See also `discrete_topology`."]
theorem Subgroup.properlyDiscontinuousSMul_of_tendsto_cofinite (S : Subgroup G)
    (hS : Tendsto S.Subtype cofinite (cocompact G)) : ProperlyDiscontinuousSMul S G :=
  {
    finite_disjoint_inter_image := by
      intro K L hK hL
      have H : Set.Finite _ := hS ((hL.prod hK).image continuous_div').compl_mem_cocompact
      rw [preimage_compl, compl_compl] at H
      convert H
      ext x
      simpa only [image_smul, mem_image, Prod.exists] using Set.smul_inter_ne_empty_iff' }
#align subgroup.properly_discontinuous_smul_of_tendsto_cofinite Subgroup.properlyDiscontinuousSMul_of_tendsto_cofinite
#align add_subgroup.properly_discontinuous_vadd_of_tendsto_cofinite AddSubgroup.properlyDiscontinuousVAdd_of_tendsto_cofinite

attribute [local semireducible] MulOpposite

/- warning: subgroup.properly_discontinuous_smul_opposite_of_tendsto_cofinite -> Subgroup.properlyDiscontinuousSMul_opposite_of_tendsto_cofinite is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] (S : Subgroup.{u1} G _inst_2), (Filter.Tendsto.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) G (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) G (Monoid.toMulOneClass.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) (Subgroup.toGroup.{u1} G _inst_2 S)))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) (fun (_x : MonoidHom.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) G (Monoid.toMulOneClass.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) (Subgroup.toGroup.{u1} G _inst_2 S)))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) => (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) -> G) (MonoidHom.hasCoeToFun.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) G (Monoid.toMulOneClass.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S) (Subgroup.toGroup.{u1} G _inst_2 S)))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) (Subgroup.subtype.{u1} G _inst_2 S)) (Filter.cofinite.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) S)) (Filter.cocompact.{u1} G _inst_1)) -> (ProperlyDiscontinuousSMul.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2)) (MulOpposite.{u1} G) (Subgroup.setLike.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) (fun (_x : Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) => (Subgroup.{u1} G _inst_2) -> (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) (Subgroup.opposite.{u1} G _inst_2) S)) G _inst_1 (MulAction.toHasSmul.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2)) (MulOpposite.{u1} G) (Subgroup.setLike.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) (fun (_x : Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) => (Subgroup.{u1} G _inst_2) -> (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) (Subgroup.opposite.{u1} G _inst_2) S)) G (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2)) (MulOpposite.{u1} G) (Subgroup.setLike.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) (fun (_x : Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) => (Subgroup.{u1} G _inst_2) -> (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) (Subgroup.opposite.{u1} G _inst_2) S)) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2)) (MulOpposite.{u1} G) (Subgroup.setLike.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) (fun (_x : Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) => (Subgroup.{u1} G _inst_2) -> (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) (Subgroup.opposite.{u1} G _inst_2) S)) (Subgroup.toGroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) (fun (_x : Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) => (Subgroup.{u1} G _inst_2) -> (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) (Subgroup.opposite.{u1} G _inst_2) S)))) (Subgroup.mulAction.{u1, u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2) G (Monoid.toOppositeMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) (fun (_x : Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) => (Subgroup.{u1} G _inst_2) -> (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) (Subgroup.opposite.{u1} G _inst_2) S))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] (S : Subgroup.{u1} G _inst_2), (Filter.Tendsto.{u1, u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x S)) G (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x S)) G (Submonoid.toMulOneClass.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Subgroup.toSubmonoid.{u1} G _inst_2 S)) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x S)) (fun (_x : Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x S)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x S)) => G) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x S)) G (Submonoid.toMulOneClass.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Subgroup.toSubmonoid.{u1} G _inst_2 S)) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x S)) G (MulOneClass.toMul.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x S)) (Submonoid.toMulOneClass.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Subgroup.toSubmonoid.{u1} G _inst_2 S))) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x S)) G (Submonoid.toMulOneClass.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Subgroup.toSubmonoid.{u1} G _inst_2 S)) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x S)) G (Submonoid.toMulOneClass.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Subgroup.toSubmonoid.{u1} G _inst_2 S)) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (MonoidHom.monoidHomClass.{u1, u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x S)) G (Submonoid.toMulOneClass.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Subgroup.toSubmonoid.{u1} G _inst_2 S)) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))) (Subgroup.subtype.{u1} G _inst_2 S)) (Filter.cofinite.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x S))) (Filter.cocompact.{u1} G _inst_1)) -> (ProperlyDiscontinuousSMul.{u1, u1} (Subtype.{succ u1} (MulOpposite.{u1} G) (fun (x : MulOpposite.{u1} G) => Membership.mem.{u1, u1} (MulOpposite.{u1} G) ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Subgroup.{u1} G _inst_2) => Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2)) S) (SetLike.instMembership.{u1, u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Subgroup.{u1} G _inst_2) => Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2)) S) (MulOpposite.{u1} G) (Subgroup.instSetLikeSubgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) x (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) (Subgroup.{u1} G _inst_2) (fun (a : Subgroup.{u1} G _inst_2) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Subgroup.{u1} G _inst_2) => Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2)) a) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) (Subgroup.opposite.{u1} G _inst_2) S))) G _inst_1 (Submonoid.smul.{u1, u1} (MulOpposite.{u1} G) G (Monoid.toMulOneClass.{u1} (MulOpposite.{u1} G) (DivInvMonoid.toMonoid.{u1} (MulOpposite.{u1} G) (Group.toDivInvMonoid.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2)))) (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) (Subgroup.toSubmonoid.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) (Subgroup.{u1} G _inst_2) (fun (_x : Subgroup.{u1} G _inst_2) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Subgroup.{u1} G _inst_2) => Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2)) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_2) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_2))) (Subgroup.opposite.{u1} G _inst_2) S))))
Case conversion may be inaccurate. Consider using '#align subgroup.properly_discontinuous_smul_opposite_of_tendsto_cofinite Subgroup.properlyDiscontinuousSMul_opposite_of_tendsto_cofiniteₓ'. -/
/-- A subgroup `S` of a topological group `G` acts on `G` properly discontinuously on the right, if
it is discrete in the sense that `S ∩ K` is finite for all compact `K`. (See also
`discrete_topology`.)

If `G` is Hausdorff, this can be combined with `t2_space_of_properly_discontinuous_smul_of_t2_space`
to show that the quotient group `G ⧸ S` is Hausdorff. -/
@[to_additive
      "A subgroup `S` of an additive topological group `G` acts on `G` properly\ndiscontinuously on the right, if it is discrete in the sense that `S ∩ K` is finite for all compact\n`K`. (See also `discrete_topology`.)\n\nIf `G` is Hausdorff, this can be combined with `t2_space_of_properly_discontinuous_vadd_of_t2_space`\nto show that the quotient group `G ⧸ S` is Hausdorff."]
theorem Subgroup.properlyDiscontinuousSMul_opposite_of_tendsto_cofinite (S : Subgroup G)
    (hS : Tendsto S.Subtype cofinite (cocompact G)) : ProperlyDiscontinuousSMul S.opposite G :=
  {
    finite_disjoint_inter_image := by
      intro K L hK hL
      have : Continuous fun p : G × G => (p.1⁻¹, p.2) := continuous_inv.prod_map continuous_id
      have H : Set.Finite _ :=
        hS ((hK.prod hL).image (continuous_mul.comp this)).compl_mem_cocompact
      rw [preimage_compl, compl_compl] at H
      convert H
      ext x
      simpa only [image_smul, mem_image, Prod.exists] using Set.op_smul_inter_ne_empty_iff }
#align subgroup.properly_discontinuous_smul_opposite_of_tendsto_cofinite Subgroup.properlyDiscontinuousSMul_opposite_of_tendsto_cofinite
#align add_subgroup.properly_discontinuous_vadd_opposite_of_tendsto_cofinite AddSubgroup.properlyDiscontinuousVAdd_opposite_of_tendsto_cofinite

end

section

/-! Some results about an open set containing the product of two sets in a topological group. -/


variable [TopologicalSpace G] [MulOneClass G] [ContinuousMul G]

/- warning: compact_open_separated_mul_right -> compact_open_separated_mul_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : MulOneClass.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G _inst_2)] {K : Set.{u1} G} {U : Set.{u1} G}, (IsCompact.{u1} G _inst_1 K) -> (IsOpen.{u1} G _inst_1 U) -> (HasSubset.Subset.{u1} (Set.{u1} G) (Set.hasSubset.{u1} G) K U) -> (Exists.{succ u1} (Set.{u1} G) (fun (V : Set.{u1} G) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (Filter.hasMem.{u1} G) V (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G _inst_2)))))) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (Filter.hasMem.{u1} G) V (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G _inst_2)))))) => HasSubset.Subset.{u1} (Set.{u1} G) (Set.hasSubset.{u1} G) (HMul.hMul.{u1, u1, u1} (Set.{u1} G) (Set.{u1} G) (Set.{u1} G) (instHMul.{u1} (Set.{u1} G) (Set.mul.{u1} G (MulOneClass.toHasMul.{u1} G _inst_2))) K V) U)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : MulOneClass.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G _inst_2)] {K : Set.{u1} G} {U : Set.{u1} G}, (IsCompact.{u1} G _inst_1 K) -> (IsOpen.{u1} G _inst_1 U) -> (HasSubset.Subset.{u1} (Set.{u1} G) (Set.instHasSubsetSet.{u1} G) K U) -> (Exists.{succ u1} (Set.{u1} G) (fun (V : Set.{u1} G) => And (Membership.mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (instMembershipSetFilter.{u1} G) V (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (MulOneClass.toOne.{u1} G _inst_2))))) (HasSubset.Subset.{u1} (Set.{u1} G) (Set.instHasSubsetSet.{u1} G) (HMul.hMul.{u1, u1, u1} (Set.{u1} G) (Set.{u1} G) (Set.{u1} G) (instHMul.{u1} (Set.{u1} G) (Set.mul.{u1} G (MulOneClass.toMul.{u1} G _inst_2))) K V) U)))
Case conversion may be inaccurate. Consider using '#align compact_open_separated_mul_right compact_open_separated_mul_rightₓ'. -/
/-- Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of `1`
  such that `K * V ⊆ U`. -/
@[to_additive
      "Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of\n`0` such that `K + V ⊆ U`."]
theorem compact_open_separated_mul_right {K U : Set G} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) : ∃ V ∈ 𝓝 (1 : G), K * V ⊆ U :=
  by
  apply hK.induction_on
  · exact ⟨univ, by simp⟩
  · rintro s t hst ⟨V, hV, hV'⟩
    exact ⟨V, hV, (mul_subset_mul_right hst).trans hV'⟩
  · rintro s t ⟨V, V_in, hV'⟩ ⟨W, W_in, hW'⟩
    use V ∩ W, inter_mem V_in W_in
    rw [union_mul]
    exact
      union_subset ((mul_subset_mul_left (V.inter_subset_left W)).trans hV')
        ((mul_subset_mul_left (V.inter_subset_right W)).trans hW')
  · intro x hx
    have := tendsto_mul (show U ∈ 𝓝 (x * 1) by simpa using hU.mem_nhds (hKU hx))
    rw [nhds_prod_eq, mem_map, mem_prod_iff] at this
    rcases this with ⟨t, ht, s, hs, h⟩
    rw [← image_subset_iff, image_mul_prod] at h
    exact ⟨t, mem_nhdsWithin_of_mem_nhds ht, s, hs, h⟩
#align compact_open_separated_mul_right compact_open_separated_mul_right
#align compact_open_separated_add_right compact_open_separated_add_right

open MulOpposite

/- warning: compact_open_separated_mul_left -> compact_open_separated_mul_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : MulOneClass.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G _inst_2)] {K : Set.{u1} G} {U : Set.{u1} G}, (IsCompact.{u1} G _inst_1 K) -> (IsOpen.{u1} G _inst_1 U) -> (HasSubset.Subset.{u1} (Set.{u1} G) (Set.hasSubset.{u1} G) K U) -> (Exists.{succ u1} (Set.{u1} G) (fun (V : Set.{u1} G) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (Filter.hasMem.{u1} G) V (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G _inst_2)))))) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (Filter.hasMem.{u1} G) V (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G _inst_2)))))) => HasSubset.Subset.{u1} (Set.{u1} G) (Set.hasSubset.{u1} G) (HMul.hMul.{u1, u1, u1} (Set.{u1} G) (Set.{u1} G) (Set.{u1} G) (instHMul.{u1} (Set.{u1} G) (Set.mul.{u1} G (MulOneClass.toHasMul.{u1} G _inst_2))) V K) U)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : MulOneClass.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G _inst_2)] {K : Set.{u1} G} {U : Set.{u1} G}, (IsCompact.{u1} G _inst_1 K) -> (IsOpen.{u1} G _inst_1 U) -> (HasSubset.Subset.{u1} (Set.{u1} G) (Set.instHasSubsetSet.{u1} G) K U) -> (Exists.{succ u1} (Set.{u1} G) (fun (V : Set.{u1} G) => And (Membership.mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (instMembershipSetFilter.{u1} G) V (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (MulOneClass.toOne.{u1} G _inst_2))))) (HasSubset.Subset.{u1} (Set.{u1} G) (Set.instHasSubsetSet.{u1} G) (HMul.hMul.{u1, u1, u1} (Set.{u1} G) (Set.{u1} G) (Set.{u1} G) (instHMul.{u1} (Set.{u1} G) (Set.mul.{u1} G (MulOneClass.toMul.{u1} G _inst_2))) V K) U)))
Case conversion may be inaccurate. Consider using '#align compact_open_separated_mul_left compact_open_separated_mul_leftₓ'. -/
/-- Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of `1`
  such that `V * K ⊆ U`. -/
@[to_additive
      "Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of\n`0` such that `V + K ⊆ U`."]
theorem compact_open_separated_mul_left {K U : Set G} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) : ∃ V ∈ 𝓝 (1 : G), V * K ⊆ U :=
  by
  rcases compact_open_separated_mul_right (hK.image continuous_op) (op_homeomorph.is_open_map U hU)
      (image_subset op hKU) with
    ⟨V, hV : V ∈ 𝓝 (op (1 : G)), hV' : op '' K * V ⊆ op '' U⟩
  refine' ⟨op ⁻¹' V, continuous_op.continuous_at hV, _⟩
  rwa [← image_preimage_eq V op_surjective, ← image_op_mul, image_subset_iff,
    preimage_image_eq _ op_injective] at hV'
#align compact_open_separated_mul_left compact_open_separated_mul_left
#align compact_open_separated_add_left compact_open_separated_add_left

end

section

variable [TopologicalSpace G] [Group G] [TopologicalGroup G]

/- warning: compact_covered_by_mul_left_translates -> compact_covered_by_mul_left_translates is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] {K : Set.{u1} G} {V : Set.{u1} G}, (IsCompact.{u1} G _inst_1 K) -> (Set.Nonempty.{u1} G (interior.{u1} G _inst_1 V)) -> (Exists.{succ u1} (Finset.{u1} G) (fun (t : Finset.{u1} G) => HasSubset.Subset.{u1} (Set.{u1} G) (Set.hasSubset.{u1} G) K (Set.unionᵢ.{u1, succ u1} G G (fun (g : G) => Set.unionᵢ.{u1, 0} G (Membership.Mem.{u1, u1} G (Finset.{u1} G) (Finset.hasMem.{u1} G) g t) (fun (H : Membership.Mem.{u1, u1} G (Finset.{u1} G) (Finset.hasMem.{u1} G) g t) => Set.preimage.{u1, u1} G G (fun (h : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) g h) V)))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] {K : Set.{u1} G} {V : Set.{u1} G}, (IsCompact.{u1} G _inst_1 K) -> (Set.Nonempty.{u1} G (interior.{u1} G _inst_1 V)) -> (Exists.{succ u1} (Finset.{u1} G) (fun (t : Finset.{u1} G) => HasSubset.Subset.{u1} (Set.{u1} G) (Set.instHasSubsetSet.{u1} G) K (Set.unionᵢ.{u1, succ u1} G G (fun (g : G) => Set.unionᵢ.{u1, 0} G (Membership.mem.{u1, u1} G (Finset.{u1} G) (Finset.instMembershipFinset.{u1} G) g t) (fun (H : Membership.mem.{u1, u1} G (Finset.{u1} G) (Finset.instMembershipFinset.{u1} G) g t) => Set.preimage.{u1, u1} G G (fun (h : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) g h) V)))))
Case conversion may be inaccurate. Consider using '#align compact_covered_by_mul_left_translates compact_covered_by_mul_left_translatesₓ'. -/
/-- A compact set is covered by finitely many left multiplicative translates of a set
  with non-empty interior. -/
@[to_additive
      "A compact set is covered by finitely many left additive translates of a set\n  with non-empty interior."]
theorem compact_covered_by_mul_left_translates {K V : Set G} (hK : IsCompact K)
    (hV : (interior V).Nonempty) : ∃ t : Finset G, K ⊆ ⋃ g ∈ t, (fun h => g * h) ⁻¹' V :=
  by
  obtain ⟨t, ht⟩ : ∃ t : Finset G, K ⊆ ⋃ x ∈ t, interior ((· * ·) x ⁻¹' V) :=
    by
    refine'
      hK.elim_finite_subcover (fun x => interior <| (· * ·) x ⁻¹' V) (fun x => isOpen_interior) _
    cases' hV with g₀ hg₀
    refine' fun g hg => mem_Union.2 ⟨g₀ * g⁻¹, _⟩
    refine' preimage_interior_subset_interior_preimage (continuous_const.mul continuous_id) _
    rwa [mem_preimage, inv_mul_cancel_right]
  exact ⟨t, subset.trans ht <| Union₂_mono fun g hg => interior_subset⟩
#align compact_covered_by_mul_left_translates compact_covered_by_mul_left_translates
#align compact_covered_by_add_left_translates compact_covered_by_add_left_translates

#print SeparableLocallyCompactGroup.sigmaCompactSpace /-
/-- Every locally compact separable topological group is σ-compact.
  Note: this is not true if we drop the topological group hypothesis. -/
@[to_additive SeparableLocallyCompactAddGroup.sigmaCompactSpace
      "Every locally\ncompact separable topological group is σ-compact.\nNote: this is not true if we drop the topological group hypothesis."]
instance (priority := 100) SeparableLocallyCompactGroup.sigmaCompactSpace [SeparableSpace G]
    [LocallyCompactSpace G] : SigmaCompactSpace G :=
  by
  obtain ⟨L, hLc, hL1⟩ := exists_compact_mem_nhds (1 : G)
  refine' ⟨⟨fun n => (fun x => x * dense_seq G n) ⁻¹' L, _, _⟩⟩
  · intro n
    exact (Homeomorph.mulRight _).isCompact_preimage.mpr hLc
  · refine' Union_eq_univ_iff.2 fun x => _
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ : (range (dense_seq G) ∩ (fun y => x * y) ⁻¹' L).Nonempty :=
      by
      rw [← (Homeomorph.mulLeft x).apply_symm_apply 1] at hL1
      exact
        (dense_range_dense_seq G).inter_nhds_nonempty
          ((Homeomorph.mulLeft x).Continuous.ContinuousAt <| hL1)
    exact ⟨n, hn⟩
#align separable_locally_compact_group.sigma_compact_space SeparableLocallyCompactGroup.sigmaCompactSpace
#align separable_locally_compact_add_group.sigma_compact_space SeparableLocallyCompactAddGroup.sigmaCompactSpace
-/

/- warning: exists_disjoint_smul_of_is_compact -> exists_disjoint_smul_of_isCompact is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] [_inst_4 : NoncompactSpace.{u1} G _inst_1] {K : Set.{u1} G} {L : Set.{u1} G}, (IsCompact.{u1} G _inst_1 K) -> (IsCompact.{u1} G _inst_1 L) -> (Exists.{succ u1} G (fun (g : G) => Disjoint.{u1} (Set.{u1} G) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} G) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} G) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} G) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} G) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} G) (Set.completeBooleanAlgebra.{u1} G)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} G) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} G) (Set.booleanAlgebra.{u1} G))) K (SMul.smul.{u1, u1} G (Set.{u1} G) (Set.smulSet.{u1, u1} G G (Mul.toSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))) g L)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] [_inst_4 : NoncompactSpace.{u1} G _inst_1] {K : Set.{u1} G} {L : Set.{u1} G}, (IsCompact.{u1} G _inst_1 K) -> (IsCompact.{u1} G _inst_1 L) -> (Exists.{succ u1} G (fun (g : G) => Disjoint.{u1} (Set.{u1} G) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} G) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} G) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} G) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} G) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} G) (Set.instCompleteBooleanAlgebraSet.{u1} G)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} G) (Preorder.toLE.{u1} (Set.{u1} G) (PartialOrder.toPreorder.{u1} (Set.{u1} G) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} G) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} G) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} G) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} G) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} G) (Set.instCompleteBooleanAlgebraSet.{u1} G)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} G) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} G) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} G) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} G) (Set.instCompleteBooleanAlgebraSet.{u1} G)))))) K (HSMul.hSMul.{u1, u1, u1} G (Set.{u1} G) (Set.{u1} G) (instHSMul.{u1, u1} G (Set.{u1} G) (Set.smulSet.{u1, u1} G G (MulAction.toSMul.{u1, u1} G G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))) g L)))
Case conversion may be inaccurate. Consider using '#align exists_disjoint_smul_of_is_compact exists_disjoint_smul_of_isCompactₓ'. -/
/-- Given two compact sets in a noncompact topological group, there is a translate of the second
one that is disjoint from the first one. -/
@[to_additive
      "Given two compact sets in a noncompact additive topological group, there is a\ntranslate of the second one that is disjoint from the first one."]
theorem exists_disjoint_smul_of_isCompact [NoncompactSpace G] {K L : Set G} (hK : IsCompact K)
    (hL : IsCompact L) : ∃ g : G, Disjoint K (g • L) :=
  by
  have A : ¬K * L⁻¹ = univ := (hK.mul hL.inv).ne_univ
  obtain ⟨g, hg⟩ : ∃ g, g ∉ K * L⁻¹ := by
    contrapose! A
    exact eq_univ_iff_forall.2 A
  refine' ⟨g, _⟩
  apply disjoint_left.2 fun a ha h'a => hg _
  rcases h'a with ⟨b, bL, rfl⟩
  refine' ⟨g * b, b⁻¹, ha, by simpa only [Set.mem_inv, inv_inv] using bL, _⟩
  simp only [smul_eq_mul, mul_inv_cancel_right]
#align exists_disjoint_smul_of_is_compact exists_disjoint_smul_of_isCompact
#align exists_disjoint_vadd_of_is_compact exists_disjoint_vadd_of_isCompact

/- warning: local_is_compact_is_closed_nhds_of_group -> local_isCompact_isClosed_nhds_of_group is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] [_inst_4 : LocallyCompactSpace.{u1} G _inst_1] {U : Set.{u1} G}, (Membership.Mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (Filter.hasMem.{u1} G) U (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))))))) -> (Exists.{succ u1} (Set.{u1} G) (fun (K : Set.{u1} G) => And (IsCompact.{u1} G _inst_1 K) (And (IsClosed.{u1} G _inst_1 K) (And (HasSubset.Subset.{u1} (Set.{u1} G) (Set.hasSubset.{u1} G) K U) (Membership.Mem.{u1, u1} G (Set.{u1} G) (Set.hasMem.{u1} G) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))))) (interior.{u1} G _inst_1 K))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] [_inst_4 : LocallyCompactSpace.{u1} G _inst_1] {U : Set.{u1} G}, (Membership.mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (instMembershipSetFilter.{u1} G) U (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))))))) -> (Exists.{succ u1} (Set.{u1} G) (fun (K : Set.{u1} G) => And (IsCompact.{u1} G _inst_1 K) (And (IsClosed.{u1} G _inst_1 K) (And (HasSubset.Subset.{u1} (Set.{u1} G) (Set.instHasSubsetSet.{u1} G) K U) (Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))))) (interior.{u1} G _inst_1 K))))))
Case conversion may be inaccurate. Consider using '#align local_is_compact_is_closed_nhds_of_group local_isCompact_isClosed_nhds_of_groupₓ'. -/
/-- In a locally compact group, any neighborhood of the identity contains a compact closed
neighborhood of the identity, even without separation assumptions on the space. -/
@[to_additive
      "In a locally compact additive group, any neighborhood of the identity contains a\ncompact closed neighborhood of the identity, even without separation assumptions on the space."]
theorem local_isCompact_isClosed_nhds_of_group [LocallyCompactSpace G] {U : Set G}
    (hU : U ∈ 𝓝 (1 : G)) : ∃ K : Set G, IsCompact K ∧ IsClosed K ∧ K ⊆ U ∧ (1 : G) ∈ interior K :=
  by
  obtain ⟨L, Lint, LU, Lcomp⟩ : ∃ (L : Set G)(H : L ∈ 𝓝 (1 : G)), L ⊆ U ∧ IsCompact L
  exact local_compact_nhds hU
  obtain ⟨V, Vnhds, hV⟩ : ∃ V ∈ 𝓝 (1 : G), ∀ v ∈ V, ∀ w ∈ V, v * w ∈ L :=
    by
    have : (fun p : G × G => p.1 * p.2) ⁻¹' L ∈ 𝓝 ((1, 1) : G × G) :=
      by
      refine' continuous_at_fst.mul continuousAt_snd _
      simpa only [mul_one] using Lint
    simpa only [div_eq_mul_inv, nhds_prod_eq, mem_prod_self_iff, prod_subset_iff, mem_preimage]
  have VL : closure V ⊆ L :=
    calc
      closure V = {(1 : G)} * closure V := by simp only [singleton_mul, one_mul, image_id']
      _ ⊆ interior V * closure V :=
        (mul_subset_mul_right
          (by simpa only [singleton_subset_iff] using mem_interior_iff_mem_nhds.2 Vnhds))
      _ = interior V * V := (is_open_interior.mul_closure _)
      _ ⊆ V * V := (mul_subset_mul_right interior_subset)
      _ ⊆ L := by
        rintro x ⟨y, z, yv, zv, rfl⟩
        exact hV _ yv _ zv
      
  exact
    ⟨closure V, isCompact_of_isClosed_subset Lcomp isClosed_closure VL, isClosed_closure,
      VL.trans LU, interior_mono subset_closure (mem_interior_iff_mem_nhds.2 Vnhds)⟩
#align local_is_compact_is_closed_nhds_of_group local_isCompact_isClosed_nhds_of_group
#align local_is_compact_is_closed_nhds_of_add_group local_isCompact_isClosed_nhds_of_addGroup

end

section

variable [TopologicalSpace G] [Group G] [TopologicalGroup G]

/- warning: nhds_mul -> nhds_mul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] (x : G) (y : G), Eq.{succ u1} (Filter.{u1} G) (nhds.{u1} G _inst_1 (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) x y)) (HMul.hMul.{u1, u1, u1} (Filter.{u1} G) (Filter.{u1} G) (Filter.{u1} G) (instHMul.{u1} (Filter.{u1} G) (Filter.instMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))) (nhds.{u1} G _inst_1 x) (nhds.{u1} G _inst_1 y))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2] (x : G) (y : G), Eq.{succ u1} (Filter.{u1} G) (nhds.{u1} G _inst_1 (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) x y)) (HMul.hMul.{u1, u1, u1} (Filter.{u1} G) (Filter.{u1} G) (Filter.{u1} G) (instHMul.{u1} (Filter.{u1} G) (Filter.instMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))) (nhds.{u1} G _inst_1 x) (nhds.{u1} G _inst_1 y))
Case conversion may be inaccurate. Consider using '#align nhds_mul nhds_mulₓ'. -/
@[to_additive]
theorem nhds_mul (x y : G) : 𝓝 (x * y) = 𝓝 x * 𝓝 y :=
  calc
    𝓝 (x * y) = map ((· * ·) x) (map (fun a => a * y) (𝓝 1 * 𝓝 1)) := by simp
    _ = map₂ (fun a b => x * (a * b * y)) (𝓝 1) (𝓝 1) := by rw [← map₂_mul, map_map₂, map_map₂]
    _ = map₂ (fun a b => x * a * (b * y)) (𝓝 1) (𝓝 1) := by simp only [mul_assoc]
    _ = 𝓝 x * 𝓝 y := by
      rw [← map_mul_left_nhds_one x, ← map_mul_right_nhds_one y, ← map₂_mul, map₂_map_left,
        map₂_map_right]
    
#align nhds_mul nhds_mul
#align nhds_add nhds_add

/- warning: nhds_mul_hom -> nhdsMulHom is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2], MulHom.{u1, u1} G (Filter.{u1} G) (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) (Filter.instMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalGroup.{u1} G _inst_1 _inst_2], MulHom.{u1, u1} G (Filter.{u1} G) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))) (Filter.instMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))
Case conversion may be inaccurate. Consider using '#align nhds_mul_hom nhdsMulHomₓ'. -/
/-- On a topological group, `𝓝 : G → filter G` can be promoted to a `mul_hom`. -/
@[to_additive
      "On an additive topological group, `𝓝 : G → filter G` can be promoted to an\n`add_hom`.",
  simps]
def nhdsMulHom : G →ₙ* Filter G where
  toFun := 𝓝
  map_mul' _ _ := nhds_mul _ _
#align nhds_mul_hom nhdsMulHom
#align nhds_add_hom nhdsAddHom

end

end FilterMul

instance {G} [TopologicalSpace G] [Group G] [TopologicalGroup G] : TopologicalAddGroup (Additive G)
    where continuous_neg := @continuous_inv G _ _ _

instance {G} [TopologicalSpace G] [AddGroup G] [TopologicalAddGroup G] :
    TopologicalGroup (Multiplicative G) where continuous_inv := @continuous_neg G _ _ _

section Quotient

variable [Group G] [TopologicalSpace G] [ContinuousMul G] {Γ : Subgroup G}

/- warning: quotient_group.has_continuous_const_smul -> QuotientGroup.continuousConstSMul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_2 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))] {Γ : Subgroup.{u1} G _inst_1}, ContinuousConstSMul.{u1, u1} G (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_1) (QuotientGroup.Subgroup.hasQuotient.{u1} G _inst_1) Γ) (QuotientGroup.Quotient.topologicalSpace.{u1} G _inst_1 _inst_2 Γ) (MulAction.toHasSmul.{u1, u1} G (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_1) (QuotientGroup.Subgroup.hasQuotient.{u1} G _inst_1) Γ) (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (MulAction.quotient.{u1, u1} G G _inst_1 (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) Γ (MulAction.left_quotientAction.{u1} G _inst_1 Γ)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_2 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))] {Γ : Subgroup.{u1} G _inst_1}, ContinuousConstSMul.{u1, u1} G (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_1) (QuotientGroup.instHasQuotientSubgroup.{u1} G _inst_1) Γ) (QuotientGroup.Quotient.topologicalSpace.{u1} G _inst_1 _inst_2 Γ) (MulAction.toSMul.{u1, u1} G (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_1) (QuotientGroup.instHasQuotientSubgroup.{u1} G _inst_1) Γ) (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (MulAction.quotient.{u1, u1} G G _inst_1 (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) Γ (MulAction.left_quotientAction.{u1} G _inst_1 Γ)))
Case conversion may be inaccurate. Consider using '#align quotient_group.has_continuous_const_smul QuotientGroup.continuousConstSMulₓ'. -/
@[to_additive]
instance QuotientGroup.continuousConstSMul : ContinuousConstSMul G (G ⧸ Γ)
    where continuous_const_smul g := by
    convert((@continuous_const _ _ _ _ g).mul continuous_id).quotient_map' _
#align quotient_group.has_continuous_const_smul QuotientGroup.continuousConstSMul
#align quotient_add_group.has_continuous_const_vadd QuotientAddGroup.continuousConstVAdd

/- warning: quotient_group.continuous_smul₁ -> QuotientGroup.continuous_smul₁ is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_2 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))] {Γ : Subgroup.{u1} G _inst_1} (x : HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_1) (QuotientGroup.Subgroup.hasQuotient.{u1} G _inst_1) Γ), Continuous.{u1, u1} G (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_1) (QuotientGroup.Subgroup.hasQuotient.{u1} G _inst_1) Γ) _inst_2 (QuotientGroup.Quotient.topologicalSpace.{u1} G _inst_1 _inst_2 Γ) (fun (g : G) => SMul.smul.{u1, u1} G (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_1) (QuotientGroup.Subgroup.hasQuotient.{u1} G _inst_1) Γ) (MulAction.toHasSmul.{u1, u1} G (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_1) (QuotientGroup.Subgroup.hasQuotient.{u1} G _inst_1) Γ) (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (MulAction.quotient.{u1, u1} G G _inst_1 (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) Γ (MulAction.left_quotientAction.{u1} G _inst_1 Γ))) g x)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_2 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))] {Γ : Subgroup.{u1} G _inst_1} (x : HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_1) (QuotientGroup.instHasQuotientSubgroup.{u1} G _inst_1) Γ), Continuous.{u1, u1} G (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_1) (QuotientGroup.instHasQuotientSubgroup.{u1} G _inst_1) Γ) _inst_2 (QuotientGroup.Quotient.topologicalSpace.{u1} G _inst_1 _inst_2 Γ) (fun (g : G) => HSMul.hSMul.{u1, u1, u1} G (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_1) (QuotientGroup.instHasQuotientSubgroup.{u1} G _inst_1) Γ) (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_1) (QuotientGroup.instHasQuotientSubgroup.{u1} G _inst_1) Γ) (instHSMul.{u1, u1} G (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_1) (QuotientGroup.instHasQuotientSubgroup.{u1} G _inst_1) Γ) (MulAction.toSMul.{u1, u1} G (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_1) (QuotientGroup.instHasQuotientSubgroup.{u1} G _inst_1) Γ) (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (MulAction.quotient.{u1, u1} G G _inst_1 (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) Γ (MulAction.left_quotientAction.{u1} G _inst_1 Γ)))) g x)
Case conversion may be inaccurate. Consider using '#align quotient_group.continuous_smul₁ QuotientGroup.continuous_smul₁ₓ'. -/
@[to_additive]
theorem QuotientGroup.continuous_smul₁ (x : G ⧸ Γ) : Continuous fun g : G => g • x :=
  by
  induction x using QuotientGroup.induction_on
  exact continuous_quotient_mk.comp (continuous_mul_right x)
#align quotient_group.continuous_smul₁ QuotientGroup.continuous_smul₁
#align quotient_add_group.continuous_smul₁ QuotientAddGroup.continuous_smul₁

/- warning: quotient_group.second_countable_topology -> QuotientGroup.secondCountableTopology is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_2 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))] {Γ : Subgroup.{u1} G _inst_1} [_inst_4 : TopologicalSpace.SecondCountableTopology.{u1} G _inst_2], TopologicalSpace.SecondCountableTopology.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_1) (QuotientGroup.Subgroup.hasQuotient.{u1} G _inst_1) Γ) (Quotient.topologicalSpace.{u1} G (MulAction.orbitRel.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1)) (MulOpposite.{u1} G) (Subgroup.setLike.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (fun (_x : Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) => (Subgroup.{u1} G _inst_1) -> (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Subgroup.opposite.{u1} G _inst_1) Γ)) G (Subgroup.toGroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (fun (_x : Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) => (Subgroup.{u1} G _inst_1) -> (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Subgroup.opposite.{u1} G _inst_1) Γ)) (Subgroup.mulAction.{u1, u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1) G (Monoid.toOppositeMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (fun (_x : Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) => (Subgroup.{u1} G _inst_1) -> (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Subgroup.opposite.{u1} G _inst_1) Γ))) _inst_2)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_2 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))] {Γ : Subgroup.{u1} G _inst_1} [_inst_4 : TopologicalSpace.SecondCountableTopology.{u1} G _inst_2], TopologicalSpace.SecondCountableTopology.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_1) (QuotientGroup.instHasQuotientSubgroup.{u1} G _inst_1) Γ) (QuotientGroup.Quotient.topologicalSpace.{u1} G _inst_1 _inst_2 Γ)
Case conversion may be inaccurate. Consider using '#align quotient_group.second_countable_topology QuotientGroup.secondCountableTopologyₓ'. -/
/-- The quotient of a second countable topological group by a subgroup is second countable. -/
@[to_additive
      "The quotient of a second countable additive topological group by a subgroup is second\ncountable."]
instance QuotientGroup.secondCountableTopology [SecondCountableTopology G] :
    SecondCountableTopology (G ⧸ Γ) :=
  ContinuousConstSMul.secondCountableTopology
#align quotient_group.second_countable_topology QuotientGroup.secondCountableTopology
#align quotient_add_group.second_countable_topology QuotientAddGroup.secondCountableTopology

end Quotient

/- warning: to_units_homeomorph -> toUnits_homeomorph is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : ContinuousInv.{u1} G _inst_2 (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))], Homeomorph.{u1, u1} G (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) _inst_2 (Units.topologicalSpace.{u1} G _inst_2 (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : ContinuousInv.{u1} G _inst_2 (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))], Homeomorph.{u1, u1} G (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) _inst_2 (Units.instTopologicalSpaceUnits.{u1} G _inst_2 (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))
Case conversion may be inaccurate. Consider using '#align to_units_homeomorph toUnits_homeomorphₓ'. -/
/-- If `G` is a group with topological `⁻¹`, then it is homeomorphic to its units. -/
@[to_additive
      " If `G` is an additive group with topological negation, then it is homeomorphic to\nits additive units."]
def toUnits_homeomorph [Group G] [TopologicalSpace G] [ContinuousInv G] : G ≃ₜ Gˣ
    where
  toEquiv := toUnits.toEquiv
  continuous_toFun := Units.continuous_iff.2 ⟨continuous_id, continuous_inv⟩
  continuous_invFun := Units.continuous_val
#align to_units_homeomorph toUnits_homeomorph
#align to_add_units_homeomorph toAddUnits_homeomorph

namespace Units

open MulOpposite (continuous_op continuous_unop)

variable [Monoid α] [TopologicalSpace α] [Monoid β] [TopologicalSpace β]

@[to_additive]
instance [ContinuousMul α] : TopologicalGroup αˣ
    where continuous_inv := Units.continuous_iff.2 <| ⟨continuous_coe_inv, continuous_val⟩

/- warning: units.homeomorph.prod_units -> Units.Homeomorph.prodUnits is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : Monoid.{u2} β] [_inst_4 : TopologicalSpace.{u2} β], Homeomorph.{max u1 u2, max u1 u2} (Units.{max u1 u2} (Prod.{u1, u2} α β) (Prod.monoid.{u1, u2} α β _inst_1 _inst_3)) (Prod.{u1, u2} (Units.{u1} α _inst_1) (Units.{u2} β _inst_3)) (Units.topologicalSpace.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_2 _inst_4) (Prod.monoid.{u1, u2} α β _inst_1 _inst_3)) (Prod.topologicalSpace.{u1, u2} (Units.{u1} α _inst_1) (Units.{u2} β _inst_3) (Units.topologicalSpace.{u1} α _inst_2 _inst_1) (Units.topologicalSpace.{u2} β _inst_4 _inst_3))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : Monoid.{u2} β] [_inst_4 : TopologicalSpace.{u2} β], Homeomorph.{max u2 u1, max u2 u1} (Units.{max u2 u1} (Prod.{u1, u2} α β) (Prod.instMonoidProd.{u1, u2} α β _inst_1 _inst_3)) (Prod.{u1, u2} (Units.{u1} α _inst_1) (Units.{u2} β _inst_3)) (Units.instTopologicalSpaceUnits.{max u1 u2} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_2 _inst_4) (Prod.instMonoidProd.{u1, u2} α β _inst_1 _inst_3)) (instTopologicalSpaceProd.{u1, u2} (Units.{u1} α _inst_1) (Units.{u2} β _inst_3) (Units.instTopologicalSpaceUnits.{u1} α _inst_2 _inst_1) (Units.instTopologicalSpaceUnits.{u2} β _inst_4 _inst_3))
Case conversion may be inaccurate. Consider using '#align units.homeomorph.prod_units Units.Homeomorph.prodUnitsₓ'. -/
/-- The topological group isomorphism between the units of a product of two monoids, and the product
of the units of each monoid. -/
@[to_additive
      "The topological group isomorphism between the additive units of a product of two\nadditive monoids, and the product of the additive units of each additive monoid."]
def Homeomorph.prodUnits : (α × β)ˣ ≃ₜ αˣ × βˣ
    where
  continuous_toFun :=
    (continuous_fst.units_map (MonoidHom.fst α β)).prod_mk
      (continuous_snd.units_map (MonoidHom.snd α β))
  continuous_invFun :=
    Units.continuous_iff.2
      ⟨continuous_val.fst'.prod_mk continuous_val.snd',
        continuous_coe_inv.fst'.prod_mk continuous_coe_inv.snd'⟩
  toEquiv := MulEquiv.prodUnits.toEquiv
#align units.homeomorph.prod_units Units.Homeomorph.prodUnits
#align add_units.homeomorph.sum_add_units AddUnits.Homeomorph.sumAddUnits

end Units

section LatticeOps

variable {ι : Sort _} [Group G]

/- warning: topological_group_Inf -> topologicalGroup_infₛ is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {ts : Set.{u1} (TopologicalSpace.{u1} G)}, (forall (t : TopologicalSpace.{u1} G), (Membership.Mem.{u1, u1} (TopologicalSpace.{u1} G) (Set.{u1} (TopologicalSpace.{u1} G)) (Set.hasMem.{u1} (TopologicalSpace.{u1} G)) t ts) -> (TopologicalGroup.{u1} G t _inst_1)) -> (TopologicalGroup.{u1} G (InfSet.infₛ.{u1} (TopologicalSpace.{u1} G) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.{u1} G) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} G) (TopologicalSpace.completeLattice.{u1} G))) ts) _inst_1)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {ts : Set.{u1} (TopologicalSpace.{u1} G)}, (forall (t : TopologicalSpace.{u1} G), (Membership.mem.{u1, u1} (TopologicalSpace.{u1} G) (Set.{u1} (TopologicalSpace.{u1} G)) (Set.instMembershipSet.{u1} (TopologicalSpace.{u1} G)) t ts) -> (TopologicalGroup.{u1} G t _inst_1)) -> (TopologicalGroup.{u1} G (InfSet.infₛ.{u1} (TopologicalSpace.{u1} G) (ConditionallyCompleteLattice.toInfSet.{u1} (TopologicalSpace.{u1} G) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} G) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} G))) ts) _inst_1)
Case conversion may be inaccurate. Consider using '#align topological_group_Inf topologicalGroup_infₛₓ'. -/
@[to_additive]
theorem topologicalGroup_infₛ {ts : Set (TopologicalSpace G)}
    (h : ∀ t ∈ ts, @TopologicalGroup G t _) : @TopologicalGroup G (infₛ ts) _ :=
  { to_continuousInv :=
      @continuousInv_infₛ _ _ _ fun t ht => @TopologicalGroup.to_continuousInv G t _ <| h t ht
    to_continuousMul :=
      @continuousMul_infₛ _ _ _ fun t ht => @TopologicalGroup.to_continuousMul G t _ <| h t ht }
#align topological_group_Inf topologicalGroup_infₛ
#align topological_add_group_Inf topologicalAddGroup_infₛ

/- warning: topological_group_infi -> topologicalGroup_infᵢ is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Group.{u1} G] {ts' : ι -> (TopologicalSpace.{u1} G)}, (forall (i : ι), TopologicalGroup.{u1} G (ts' i) _inst_1) -> (TopologicalGroup.{u1} G (infᵢ.{u1, u2} (TopologicalSpace.{u1} G) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.{u1} G) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} G) (TopologicalSpace.completeLattice.{u1} G))) ι (fun (i : ι) => ts' i)) _inst_1)
but is expected to have type
  forall {G : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : Group.{u2} G] {ts' : ι -> (TopologicalSpace.{u2} G)}, (forall (i : ι), TopologicalGroup.{u2} G (ts' i) _inst_1) -> (TopologicalGroup.{u2} G (infᵢ.{u2, u1} (TopologicalSpace.{u2} G) (ConditionallyCompleteLattice.toInfSet.{u2} (TopologicalSpace.{u2} G) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} G) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u2} G))) ι (fun (i : ι) => ts' i)) _inst_1)
Case conversion may be inaccurate. Consider using '#align topological_group_infi topologicalGroup_infᵢₓ'. -/
@[to_additive]
theorem topologicalGroup_infᵢ {ts' : ι → TopologicalSpace G}
    (h' : ∀ i, @TopologicalGroup G (ts' i) _) : @TopologicalGroup G (⨅ i, ts' i) _ :=
  by
  rw [← infₛ_range]
  exact topologicalGroup_infₛ (set.forall_range_iff.mpr h')
#align topological_group_infi topologicalGroup_infᵢ
#align topological_add_group_infi topologicalAddGroup_infᵢ

/- warning: topological_group_inf -> topologicalGroup_inf is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {t₁ : TopologicalSpace.{u1} G} {t₂ : TopologicalSpace.{u1} G}, (TopologicalGroup.{u1} G t₁ _inst_1) -> (TopologicalGroup.{u1} G t₂ _inst_1) -> (TopologicalGroup.{u1} G (Inf.inf.{u1} (TopologicalSpace.{u1} G) (SemilatticeInf.toHasInf.{u1} (TopologicalSpace.{u1} G) (Lattice.toSemilatticeInf.{u1} (TopologicalSpace.{u1} G) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} G) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} G) (TopologicalSpace.completeLattice.{u1} G))))) t₁ t₂) _inst_1)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {t₁ : TopologicalSpace.{u1} G} {t₂ : TopologicalSpace.{u1} G}, (TopologicalGroup.{u1} G t₁ _inst_1) -> (TopologicalGroup.{u1} G t₂ _inst_1) -> (TopologicalGroup.{u1} G (Inf.inf.{u1} (TopologicalSpace.{u1} G) (Lattice.toInf.{u1} (TopologicalSpace.{u1} G) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} G) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} G) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} G)))) t₁ t₂) _inst_1)
Case conversion may be inaccurate. Consider using '#align topological_group_inf topologicalGroup_infₓ'. -/
@[to_additive]
theorem topologicalGroup_inf {t₁ t₂ : TopologicalSpace G} (h₁ : @TopologicalGroup G t₁ _)
    (h₂ : @TopologicalGroup G t₂ _) : @TopologicalGroup G (t₁ ⊓ t₂) _ :=
  by
  rw [inf_eq_infᵢ]
  refine' topologicalGroup_infᵢ fun b => _
  cases b <;> assumption
#align topological_group_inf topologicalGroup_inf
#align topological_add_group_inf topologicalAddGroup_inf

end LatticeOps

/-!
### Lattice of group topologies

We define a type class `group_topology α` which endows a group `α` with a topology such that all
group operations are continuous.

Group topologies on a fixed group `α` are ordered, by reverse inclusion. They form a complete
lattice, with `⊥` the discrete topology and `⊤` the indiscrete topology.

Any function `f : α → β` induces `coinduced f : topological_space α → group_topology β`.

The additive version `add_group_topology α` and corresponding results are provided as well.
-/


#print GroupTopology /-
/-- A group topology on a group `α` is a topology for which multiplication and inversion
are continuous. -/
structure GroupTopology (α : Type u) [Group α] extends TopologicalSpace α, TopologicalGroup α :
  Type u
#align group_topology GroupTopology
-/

#print AddGroupTopology /-
/-- An additive group topology on an additive group `α` is a topology for which addition and
  negation are continuous. -/
structure AddGroupTopology (α : Type u) [AddGroup α] extends TopologicalSpace α,
  TopologicalAddGroup α : Type u
#align add_group_topology AddGroupTopology
-/

attribute [to_additive] GroupTopology

namespace GroupTopology

variable [Group α]

/- warning: group_topology.continuous_mul' -> GroupTopology.continuous_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] (g : GroupTopology.{u1} α _inst_1), Continuous.{u1, u1} (Prod.{u1, u1} α α) α (Prod.topologicalSpace.{u1, u1} α α (GroupTopology.toTopologicalSpace.{u1} α _inst_1 g) (GroupTopology.toTopologicalSpace.{u1} α _inst_1 g)) (GroupTopology.toTopologicalSpace.{u1} α _inst_1 g) (fun (p : Prod.{u1, u1} α α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] (g : GroupTopology.{u1} α _inst_1), Continuous.{u1, u1} (Prod.{u1, u1} α α) α (instTopologicalSpaceProd.{u1, u1} α α (GroupTopology.toTopologicalSpace.{u1} α _inst_1 g) (GroupTopology.toTopologicalSpace.{u1} α _inst_1 g)) (GroupTopology.toTopologicalSpace.{u1} α _inst_1 g) (fun (p : Prod.{u1, u1} α α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))
Case conversion may be inaccurate. Consider using '#align group_topology.continuous_mul' GroupTopology.continuous_mul'ₓ'. -/
/-- A version of the global `continuous_mul` suitable for dot notation. -/
@[to_additive "A version of the global `continuous_add` suitable for dot notation."]
theorem continuous_mul' (g : GroupTopology α) :
    haveI := g.to_topological_space
    Continuous fun p : α × α => p.1 * p.2 :=
  by
  letI := g.to_topological_space
  haveI := g.to_topological_group
  exact continuous_mul
#align group_topology.continuous_mul' GroupTopology.continuous_mul'
#align add_group_topology.continuous_add' AddGroupTopology.continuous_add'

/- warning: group_topology.continuous_inv' -> GroupTopology.continuous_inv' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] (g : GroupTopology.{u1} α _inst_1), Continuous.{u1, u1} α α (GroupTopology.toTopologicalSpace.{u1} α _inst_1 g) (GroupTopology.toTopologicalSpace.{u1} α _inst_1 g) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] (g : GroupTopology.{u1} α _inst_1), Continuous.{u1, u1} α α (GroupTopology.toTopologicalSpace.{u1} α _inst_1 g) (GroupTopology.toTopologicalSpace.{u1} α _inst_1 g) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align group_topology.continuous_inv' GroupTopology.continuous_inv'ₓ'. -/
/-- A version of the global `continuous_inv` suitable for dot notation. -/
@[to_additive "A version of the global `continuous_neg` suitable for dot notation."]
theorem continuous_inv' (g : GroupTopology α) :
    haveI := g.to_topological_space
    Continuous (Inv.inv : α → α) :=
  by
  letI := g.to_topological_space
  haveI := g.to_topological_group
  exact continuous_inv
#align group_topology.continuous_inv' GroupTopology.continuous_inv'
#align add_group_topology.continuous_neg' AddGroupTopology.continuous_neg'

#print GroupTopology.toTopologicalSpace_injective /-
@[to_additive]
theorem toTopologicalSpace_injective :
    Function.Injective (toTopologicalSpace : GroupTopology α → TopologicalSpace α) := fun f g h =>
  by
  cases f
  cases g
  congr
#align group_topology.to_topological_space_injective GroupTopology.toTopologicalSpace_injective
#align add_group_topology.to_topological_space_injective AddGroupTopology.toTopologicalSpace_injective
-/

#print GroupTopology.ext' /-
@[ext, to_additive]
theorem ext' {f g : GroupTopology α} (h : f.IsOpen = g.IsOpen) : f = g :=
  toTopologicalSpace_injective <| topologicalSpace_eq h
#align group_topology.ext' GroupTopology.ext'
#align add_group_topology.ext' AddGroupTopology.ext'
-/

/-- The ordering on group topologies on the group `γ`. `t ≤ s` if every set open in `s` is also open
in `t` (`t` is finer than `s`). -/
@[to_additive
      "The ordering on group topologies on the group `γ`. `t ≤ s` if every set open in `s`\nis also open in `t` (`t` is finer than `s`)."]
instance : PartialOrder (GroupTopology α) :=
  PartialOrder.lift toTopologicalSpace toTopologicalSpace_injective

/- warning: group_topology.to_topological_space_le -> GroupTopology.toTopologicalSpace_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {x : GroupTopology.{u1} α _inst_1} {y : GroupTopology.{u1} α _inst_1}, Iff (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toLE.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α))) (GroupTopology.toTopologicalSpace.{u1} α _inst_1 x) (GroupTopology.toTopologicalSpace.{u1} α _inst_1 y)) (LE.le.{u1} (GroupTopology.{u1} α _inst_1) (Preorder.toLE.{u1} (GroupTopology.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (GroupTopology.{u1} α _inst_1) (GroupTopology.partialOrder.{u1} α _inst_1))) x y)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {x : GroupTopology.{u1} α _inst_1} {y : GroupTopology.{u1} α _inst_1}, Iff (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toLE.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u1} α))) (GroupTopology.toTopologicalSpace.{u1} α _inst_1 x) (GroupTopology.toTopologicalSpace.{u1} α _inst_1 y)) (LE.le.{u1} (GroupTopology.{u1} α _inst_1) (Preorder.toLE.{u1} (GroupTopology.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (GroupTopology.{u1} α _inst_1) (GroupTopology.instPartialOrderGroupTopology.{u1} α _inst_1))) x y)
Case conversion may be inaccurate. Consider using '#align group_topology.to_topological_space_le GroupTopology.toTopologicalSpace_leₓ'. -/
@[simp, to_additive]
theorem toTopologicalSpace_le {x y : GroupTopology α} :
    x.toTopologicalSpace ≤ y.toTopologicalSpace ↔ x ≤ y :=
  Iff.rfl
#align group_topology.to_topological_space_le GroupTopology.toTopologicalSpace_le
#align add_group_topology.to_topological_space_le AddGroupTopology.toTopologicalSpace_le

@[to_additive]
instance : Top (GroupTopology α) :=
  ⟨{  toTopologicalSpace := ⊤
      continuous_mul := continuous_top
      continuous_inv := continuous_top }⟩

/- warning: group_topology.to_topological_space_top -> GroupTopology.toTopologicalSpace_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α], Eq.{succ u1} (TopologicalSpace.{u1} α) (GroupTopology.toTopologicalSpace.{u1} α _inst_1 (Top.top.{u1} (GroupTopology.{u1} α _inst_1) (GroupTopology.hasTop.{u1} α _inst_1))) (Top.top.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toHasTop.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α], Eq.{succ u1} (TopologicalSpace.{u1} α) (GroupTopology.toTopologicalSpace.{u1} α _inst_1 (Top.top.{u1} (GroupTopology.{u1} α _inst_1) (GroupTopology.instTopGroupTopology.{u1} α _inst_1))) (Top.top.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toTop.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α)))
Case conversion may be inaccurate. Consider using '#align group_topology.to_topological_space_top GroupTopology.toTopologicalSpace_topₓ'. -/
@[simp, to_additive]
theorem toTopologicalSpace_top : (⊤ : GroupTopology α).toTopologicalSpace = ⊤ :=
  rfl
#align group_topology.to_topological_space_top GroupTopology.toTopologicalSpace_top
#align add_group_topology.to_topological_space_top AddGroupTopology.toTopologicalSpace_top

@[to_additive]
instance : Bot (GroupTopology α) :=
  ⟨{  toTopologicalSpace := ⊥
      continuous_mul := by
        letI : TopologicalSpace α := ⊥
        haveI := discreteTopology_bot α
        continuity
      continuous_inv := continuous_bot }⟩

/- warning: group_topology.to_topological_space_bot -> GroupTopology.toTopologicalSpace_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α], Eq.{succ u1} (TopologicalSpace.{u1} α) (GroupTopology.toTopologicalSpace.{u1} α _inst_1 (Bot.bot.{u1} (GroupTopology.{u1} α _inst_1) (GroupTopology.hasBot.{u1} α _inst_1))) (Bot.bot.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toHasBot.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α], Eq.{succ u1} (TopologicalSpace.{u1} α) (GroupTopology.toTopologicalSpace.{u1} α _inst_1 (Bot.bot.{u1} (GroupTopology.{u1} α _inst_1) (GroupTopology.instBotGroupTopology.{u1} α _inst_1))) (Bot.bot.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toBot.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α)))
Case conversion may be inaccurate. Consider using '#align group_topology.to_topological_space_bot GroupTopology.toTopologicalSpace_botₓ'. -/
@[simp, to_additive]
theorem toTopologicalSpace_bot : (⊥ : GroupTopology α).toTopologicalSpace = ⊥ :=
  rfl
#align group_topology.to_topological_space_bot GroupTopology.toTopologicalSpace_bot
#align add_group_topology.to_topological_space_bot AddGroupTopology.toTopologicalSpace_bot

@[to_additive]
instance : BoundedOrder (GroupTopology α) where
  top := ⊤
  le_top x := show x.toTopologicalSpace ≤ ⊤ from le_top
  bot := ⊥
  bot_le x := show ⊥ ≤ x.toTopologicalSpace from bot_le

@[to_additive]
instance : Inf (GroupTopology α) where inf x y := ⟨x.1 ⊓ y.1, topologicalGroup_inf x.2 y.2⟩

/- warning: group_topology.to_topological_space_inf -> GroupTopology.toTopologicalSpace_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] (x : GroupTopology.{u1} α _inst_1) (y : GroupTopology.{u1} α _inst_1), Eq.{succ u1} (TopologicalSpace.{u1} α) (GroupTopology.toTopologicalSpace.{u1} α _inst_1 (Inf.inf.{u1} (GroupTopology.{u1} α _inst_1) (GroupTopology.hasInf.{u1} α _inst_1) x y)) (Inf.inf.{u1} (TopologicalSpace.{u1} α) (SemilatticeInf.toHasInf.{u1} (TopologicalSpace.{u1} α) (Lattice.toSemilatticeInf.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))))) (GroupTopology.toTopologicalSpace.{u1} α _inst_1 x) (GroupTopology.toTopologicalSpace.{u1} α _inst_1 y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] (x : GroupTopology.{u1} α _inst_1) (y : GroupTopology.{u1} α _inst_1), Eq.{succ u1} (TopologicalSpace.{u1} α) (GroupTopology.toTopologicalSpace.{u1} α _inst_1 (Inf.inf.{u1} (GroupTopology.{u1} α _inst_1) (GroupTopology.instInfGroupTopology.{u1} α _inst_1) x y)) (Inf.inf.{u1} (TopologicalSpace.{u1} α) (Lattice.toInf.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α)))) (GroupTopology.toTopologicalSpace.{u1} α _inst_1 x) (GroupTopology.toTopologicalSpace.{u1} α _inst_1 y))
Case conversion may be inaccurate. Consider using '#align group_topology.to_topological_space_inf GroupTopology.toTopologicalSpace_infₓ'. -/
@[simp, to_additive]
theorem toTopologicalSpace_inf (x y : GroupTopology α) :
    (x ⊓ y).toTopologicalSpace = x.toTopologicalSpace ⊓ y.toTopologicalSpace :=
  rfl
#align group_topology.to_topological_space_inf GroupTopology.toTopologicalSpace_inf
#align add_group_topology.to_topological_space_inf AddGroupTopology.toTopologicalSpace_inf

@[to_additive]
instance : SemilatticeInf (GroupTopology α) :=
  toTopologicalSpace_injective.SemilatticeInf _ toTopologicalSpace_inf

@[to_additive]
instance : Inhabited (GroupTopology α) :=
  ⟨⊤⟩

-- mathport name: exprcont
local notation "cont" => @Continuous _ _

/-- Infimum of a collection of group topologies. -/
@[to_additive "Infimum of a collection of additive group topologies"]
instance : InfSet (GroupTopology α)
    where infₛ S :=
    ⟨infₛ (toTopologicalSpace '' S), topologicalGroup_infₛ <| ball_image_iff.2 fun t ht => t.2⟩

/- warning: group_topology.to_topological_space_Inf -> GroupTopology.toTopologicalSpace_infₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] (s : Set.{u1} (GroupTopology.{u1} α _inst_1)), Eq.{succ u1} (TopologicalSpace.{u1} α) (GroupTopology.toTopologicalSpace.{u1} α _inst_1 (InfSet.infₛ.{u1} (GroupTopology.{u1} α _inst_1) (GroupTopology.hasInf.{u1} α _inst_1) s)) (InfSet.infₛ.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))) (Set.image.{u1, u1} (GroupTopology.{u1} α _inst_1) (TopologicalSpace.{u1} α) (GroupTopology.toTopologicalSpace.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] (s : Set.{u1} (GroupTopology.{u1} α _inst_1)), Eq.{succ u1} (TopologicalSpace.{u1} α) (GroupTopology.toTopologicalSpace.{u1} α _inst_1 (InfSet.infₛ.{u1} (GroupTopology.{u1} α _inst_1) (GroupTopology.instInfSetGroupTopology.{u1} α _inst_1) s)) (InfSet.infₛ.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α))) (Set.image.{u1, u1} (GroupTopology.{u1} α _inst_1) (TopologicalSpace.{u1} α) (GroupTopology.toTopologicalSpace.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align group_topology.to_topological_space_Inf GroupTopology.toTopologicalSpace_infₛₓ'. -/
@[simp, to_additive]
theorem toTopologicalSpace_infₛ (s : Set (GroupTopology α)) :
    (infₛ s).toTopologicalSpace = infₛ (toTopologicalSpace '' s) :=
  rfl
#align group_topology.to_topological_space_Inf GroupTopology.toTopologicalSpace_infₛ
#align add_group_topology.to_topological_space_Inf AddGroupTopology.toTopologicalSpace_infₛ

/- warning: group_topology.to_topological_space_infi -> GroupTopology.toTopologicalSpace_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {ι : Sort.{u2}} (s : ι -> (GroupTopology.{u1} α _inst_1)), Eq.{succ u1} (TopologicalSpace.{u1} α) (GroupTopology.toTopologicalSpace.{u1} α _inst_1 (infᵢ.{u1, u2} (GroupTopology.{u1} α _inst_1) (GroupTopology.hasInf.{u1} α _inst_1) ι (fun (i : ι) => s i))) (infᵢ.{u1, u2} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))) ι (fun (i : ι) => GroupTopology.toTopologicalSpace.{u1} α _inst_1 (s i)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : Group.{u2} α] {ι : Sort.{u1}} (s : ι -> (GroupTopology.{u2} α _inst_1)), Eq.{succ u2} (TopologicalSpace.{u2} α) (GroupTopology.toTopologicalSpace.{u2} α _inst_1 (infᵢ.{u2, u1} (GroupTopology.{u2} α _inst_1) (GroupTopology.instInfSetGroupTopology.{u2} α _inst_1) ι (fun (i : ι) => s i))) (infᵢ.{u2, u1} (TopologicalSpace.{u2} α) (ConditionallyCompleteLattice.toInfSet.{u2} (TopologicalSpace.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u2} α))) ι (fun (i : ι) => GroupTopology.toTopologicalSpace.{u2} α _inst_1 (s i)))
Case conversion may be inaccurate. Consider using '#align group_topology.to_topological_space_infi GroupTopology.toTopologicalSpace_infᵢₓ'. -/
@[simp, to_additive]
theorem toTopologicalSpace_infᵢ {ι} (s : ι → GroupTopology α) :
    (⨅ i, s i).toTopologicalSpace = ⨅ i, (s i).toTopologicalSpace :=
  congr_arg infₛ (range_comp _ _).symm
#align group_topology.to_topological_space_infi GroupTopology.toTopologicalSpace_infᵢ
#align add_group_topology.to_topological_space_infi AddGroupTopology.toTopologicalSpace_infᵢ

/-- Group topologies on `γ` form a complete lattice, with `⊥` the discrete topology and `⊤` the
indiscrete topology.

The infimum of a collection of group topologies is the topology generated by all their open sets
(which is a group topology).

The supremum of two group topologies `s` and `t` is the infimum of the family of all group
topologies contained in the intersection of `s` and `t`. -/
@[to_additive
      "Group topologies on `γ` form a complete lattice, with `⊥` the discrete topology and\n`⊤` the indiscrete topology.\n\nThe infimum of a collection of group topologies is the topology generated by all their open sets\n(which is a group topology).\n\nThe supremum of two group topologies `s` and `t` is the infimum of the family of all group\ntopologies contained in the intersection of `s` and `t`."]
instance : CompleteSemilatticeInf (GroupTopology α) :=
  { GroupTopology.hasInf,
    GroupTopology.partialOrder with
    inf_le := fun S a haS => toTopologicalSpace_le.1 <| infₛ_le ⟨a, haS, rfl⟩
    le_inf := by
      intro S a hab
      apply topological_space.complete_lattice.le_Inf
      rintro _ ⟨b, hbS, rfl⟩
      exact hab b hbS }

@[to_additive]
instance : CompleteLattice (GroupTopology α) :=
  { GroupTopology.boundedOrder, GroupTopology.semilatticeInf,
    completeLatticeOfCompleteSemilatticeInf
      _ with
    inf := (· ⊓ ·)
    top := ⊤
    bot := ⊥ }

#print GroupTopology.coinduced /-
/-- Given `f : α → β` and a topology on `α`, the coinduced group topology on `β` is the finest
topology such that `f` is continuous and `β` is a topological group. -/
@[to_additive
      "Given `f : α → β` and a topology on `α`, the coinduced additive group topology on `β`\nis the finest topology such that `f` is continuous and `β` is a topological additive group."]
def coinduced {α β : Type _} [t : TopologicalSpace α] [Group β] (f : α → β) : GroupTopology β :=
  infₛ { b : GroupTopology β | TopologicalSpace.coinduced f t ≤ b.toTopologicalSpace }
#align group_topology.coinduced GroupTopology.coinduced
#align add_group_topology.coinduced AddGroupTopology.coinduced
-/

/- warning: group_topology.coinduced_continuous -> GroupTopology.coinduced_continuous is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [t : TopologicalSpace.{u1} α] [_inst_2 : Group.{u2} β] (f : α -> β), Continuous.{u1, u2} α β t (GroupTopology.toTopologicalSpace.{u2} β _inst_2 (GroupTopology.coinduced.{u1, u2} α β t _inst_2 f)) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [t : TopologicalSpace.{u2} α] [_inst_2 : Group.{u1} β] (f : α -> β), Continuous.{u2, u1} α β t (GroupTopology.toTopologicalSpace.{u1} β _inst_2 (GroupTopology.coinduced.{u2, u1} α β t _inst_2 f)) f
Case conversion may be inaccurate. Consider using '#align group_topology.coinduced_continuous GroupTopology.coinduced_continuousₓ'. -/
@[to_additive]
theorem coinduced_continuous {α β : Type _} [t : TopologicalSpace α] [Group β] (f : α → β) :
    cont t (coinduced f).toTopologicalSpace f :=
  by
  rw [continuous_infₛ_rng]
  rintro _ ⟨t', ht', rfl⟩
  exact continuous_iff_coinduced_le.2 ht'
#align group_topology.coinduced_continuous GroupTopology.coinduced_continuous
#align add_group_topology.coinduced_continuous AddGroupTopology.coinduced_continuous

end GroupTopology

