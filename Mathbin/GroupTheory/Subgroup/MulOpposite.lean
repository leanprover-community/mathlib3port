/-
Copyright (c) 2022 Alex Kontorovich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich

! This file was ported from Lean 3 source module group_theory.subgroup.mul_opposite
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Subgroup.Actions

/-!
# Mul-opposite subgroups

## Tags
subgroup, subgroups

-/


variable {G : Type _} [Group G]

namespace Subgroup

/- warning: subgroup.opposite -> Subgroup.opposite is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G], Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G], Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))
Case conversion may be inaccurate. Consider using '#align subgroup.opposite Subgroup.oppositeₓ'. -/
/-- A subgroup `H` of `G` determines a subgroup `H.opposite` of the opposite group `Gᵐᵒᵖ`. -/
@[to_additive
      "An additive subgroup `H` of `G` determines an additive subgroup `H.opposite` of the\n  opposite additive group `Gᵃᵒᵖ`."]
def opposite : Subgroup G ≃ Subgroup Gᵐᵒᵖ
    where
  toFun H :=
    { carrier := MulOpposite.unop ⁻¹' (H : Set G)
      one_mem' := H.one_mem
      mul_mem' := fun a b ha hb => H.mul_mem hb ha
      inv_mem' := fun a => H.inv_mem }
  invFun H :=
    { carrier := MulOpposite.op ⁻¹' (H : Set Gᵐᵒᵖ)
      one_mem' := H.one_mem
      mul_mem' := fun a b ha hb => H.mul_mem hb ha
      inv_mem' := fun a => H.inv_mem }
  left_inv H := SetLike.coe_injective rfl
  right_inv H := SetLike.coe_injective rfl
#align subgroup.opposite Subgroup.opposite
#align add_subgroup.opposite AddSubgroup.opposite

/- warning: subgroup.opposite_equiv -> Subgroup.oppositeEquiv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1), Equiv.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1)) (MulOpposite.{u1} G) (Subgroup.setLike.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (fun (_x : Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) => (Subgroup.{u1} G _inst_1) -> (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Subgroup.opposite.{u1} G _inst_1) H))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1), Equiv.{succ u1, succ u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H)) (Subtype.{succ u1} (MulOpposite.{u1} G) (fun (x : MulOpposite.{u1} G) => Membership.mem.{u1, u1} (MulOpposite.{u1} G) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subgroup.{u1} G _inst_1) => Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) H) (SetLike.instMembership.{u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subgroup.{u1} G _inst_1) => Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) H) (MulOpposite.{u1} G) (Subgroup.instSetLikeSubgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) x (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) (Subgroup.{u1} G _inst_1) (fun (a : Subgroup.{u1} G _inst_1) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subgroup.{u1} G _inst_1) => Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) a) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) (Equiv.instEquivLikeEquiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))))) (Subgroup.opposite.{u1} G _inst_1) H)))
Case conversion may be inaccurate. Consider using '#align subgroup.opposite_equiv Subgroup.oppositeEquivₓ'. -/
/-- Bijection between a subgroup `H` and its opposite. -/
@[to_additive "Bijection between an additive subgroup `H` and its opposite.", simps]
def oppositeEquiv (H : Subgroup G) : H ≃ H.opposite :=
  MulOpposite.opEquiv.subtypeEquiv fun _ => Iff.rfl
#align subgroup.opposite_equiv Subgroup.oppositeEquiv
#align add_subgroup.opposite_equiv AddSubgroup.oppositeEquiv

@[to_additive]
instance (H : Subgroup G) [Encodable H] : Encodable H.opposite :=
  Encodable.ofEquiv H H.oppositeEquiv.symm

@[to_additive]
instance (H : Subgroup G) [Countable H] : Countable H.opposite :=
  Countable.of_equiv H H.oppositeEquiv

/- warning: subgroup.smul_opposite_mul -> Subgroup.smul_opposite_mul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} (x : G) (g : G) (h : coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1)) (MulOpposite.{u1} G) (Subgroup.setLike.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (fun (_x : Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) => (Subgroup.{u1} G _inst_1) -> (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Subgroup.opposite.{u1} G _inst_1) H)), Eq.{succ u1} G (SMul.smul.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1)) (MulOpposite.{u1} G) (Subgroup.setLike.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (fun (_x : Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) => (Subgroup.{u1} G _inst_1) -> (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Subgroup.opposite.{u1} G _inst_1) H)) G (MulAction.toHasSmul.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1)) (MulOpposite.{u1} G) (Subgroup.setLike.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (fun (_x : Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) => (Subgroup.{u1} G _inst_1) -> (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Subgroup.opposite.{u1} G _inst_1) H)) G (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1)) (MulOpposite.{u1} G) (Subgroup.setLike.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (fun (_x : Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) => (Subgroup.{u1} G _inst_1) -> (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Subgroup.opposite.{u1} G _inst_1) H)) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1)) (MulOpposite.{u1} G) (Subgroup.setLike.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (fun (_x : Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) => (Subgroup.{u1} G _inst_1) -> (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Subgroup.opposite.{u1} G _inst_1) H)) (Subgroup.toGroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (fun (_x : Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) => (Subgroup.{u1} G _inst_1) -> (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Subgroup.opposite.{u1} G _inst_1) H)))) (Subgroup.mulAction.{u1, u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1) G (Monoid.toOppositeMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (fun (_x : Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) => (Subgroup.{u1} G _inst_1) -> (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Subgroup.opposite.{u1} G _inst_1) H))) h (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) g x)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) g (SMul.smul.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1)) (MulOpposite.{u1} G) (Subgroup.setLike.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (fun (_x : Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) => (Subgroup.{u1} G _inst_1) -> (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Subgroup.opposite.{u1} G _inst_1) H)) G (MulAction.toHasSmul.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1)) (MulOpposite.{u1} G) (Subgroup.setLike.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (fun (_x : Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) => (Subgroup.{u1} G _inst_1) -> (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Subgroup.opposite.{u1} G _inst_1) H)) G (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1)) (MulOpposite.{u1} G) (Subgroup.setLike.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (fun (_x : Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) => (Subgroup.{u1} G _inst_1) -> (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Subgroup.opposite.{u1} G _inst_1) H)) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1)) (MulOpposite.{u1} G) (Subgroup.setLike.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (fun (_x : Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) => (Subgroup.{u1} G _inst_1) -> (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Subgroup.opposite.{u1} G _inst_1) H)) (Subgroup.toGroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (fun (_x : Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) => (Subgroup.{u1} G _inst_1) -> (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Subgroup.opposite.{u1} G _inst_1) H)))) (Subgroup.mulAction.{u1, u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1) G (Monoid.toOppositeMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (fun (_x : Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) => (Subgroup.{u1} G _inst_1) -> (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.group.{u1} G _inst_1))) (Subgroup.opposite.{u1} G _inst_1) H))) h x))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} (x : G) (g : G) (h : Subtype.{succ u1} (MulOpposite.{u1} G) (fun (x : MulOpposite.{u1} G) => Membership.mem.{u1, u1} (MulOpposite.{u1} G) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subgroup.{u1} G _inst_1) => Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) H) (SetLike.instMembership.{u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subgroup.{u1} G _inst_1) => Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) H) (MulOpposite.{u1} G) (Subgroup.instSetLikeSubgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) x (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) (Subgroup.{u1} G _inst_1) (fun (a : Subgroup.{u1} G _inst_1) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subgroup.{u1} G _inst_1) => Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) a) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) (Equiv.instEquivLikeEquiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))))) (Subgroup.opposite.{u1} G _inst_1) H))), Eq.{succ u1} G (HSMul.hSMul.{u1, u1, u1} (Subtype.{succ u1} (MulOpposite.{u1} G) (fun (x : MulOpposite.{u1} G) => Membership.mem.{u1, u1} (MulOpposite.{u1} G) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subgroup.{u1} G _inst_1) => Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) H) (SetLike.instMembership.{u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subgroup.{u1} G _inst_1) => Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) H) (MulOpposite.{u1} G) (Subgroup.instSetLikeSubgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) x (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) (Subgroup.{u1} G _inst_1) (fun (a : Subgroup.{u1} G _inst_1) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subgroup.{u1} G _inst_1) => Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) a) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) (Equiv.instEquivLikeEquiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))))) (Subgroup.opposite.{u1} G _inst_1) H))) G G (instHSMul.{u1, u1} (Subtype.{succ u1} (MulOpposite.{u1} G) (fun (x : MulOpposite.{u1} G) => Membership.mem.{u1, u1} (MulOpposite.{u1} G) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subgroup.{u1} G _inst_1) => Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) H) (SetLike.instMembership.{u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subgroup.{u1} G _inst_1) => Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) H) (MulOpposite.{u1} G) (Subgroup.instSetLikeSubgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) x (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) (Subgroup.{u1} G _inst_1) (fun (a : Subgroup.{u1} G _inst_1) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subgroup.{u1} G _inst_1) => Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) a) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) (Equiv.instEquivLikeEquiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))))) (Subgroup.opposite.{u1} G _inst_1) H))) G (Submonoid.instSMulSubtypeMemSubmonoidInstMembershipInstSetLikeSubmonoid.{u1, u1} (MulOpposite.{u1} G) G (Monoid.toMulOneClass.{u1} (MulOpposite.{u1} G) (DivInvMonoid.toMonoid.{u1} (MulOpposite.{u1} G) (Group.toDivInvMonoid.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)))) (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Subgroup.toSubmonoid.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) (Subgroup.{u1} G _inst_1) (fun (a : Subgroup.{u1} G _inst_1) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subgroup.{u1} G _inst_1) => Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) a) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) (Equiv.instEquivLikeEquiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))))) (Subgroup.opposite.{u1} G _inst_1) H)))) h (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) g x)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) g (HSMul.hSMul.{u1, u1, u1} (Subtype.{succ u1} (MulOpposite.{u1} G) (fun (x : MulOpposite.{u1} G) => Membership.mem.{u1, u1} (MulOpposite.{u1} G) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subgroup.{u1} G _inst_1) => Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) H) (SetLike.instMembership.{u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subgroup.{u1} G _inst_1) => Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) H) (MulOpposite.{u1} G) (Subgroup.instSetLikeSubgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) x (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) (Subgroup.{u1} G _inst_1) (fun (a : Subgroup.{u1} G _inst_1) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subgroup.{u1} G _inst_1) => Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) a) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) (Equiv.instEquivLikeEquiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))))) (Subgroup.opposite.{u1} G _inst_1) H))) G G (instHSMul.{u1, u1} (Subtype.{succ u1} (MulOpposite.{u1} G) (fun (x : MulOpposite.{u1} G) => Membership.mem.{u1, u1} (MulOpposite.{u1} G) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subgroup.{u1} G _inst_1) => Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) H) (SetLike.instMembership.{u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subgroup.{u1} G _inst_1) => Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) H) (MulOpposite.{u1} G) (Subgroup.instSetLikeSubgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) x (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) (Subgroup.{u1} G _inst_1) (fun (a : Subgroup.{u1} G _inst_1) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subgroup.{u1} G _inst_1) => Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) a) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) (Equiv.instEquivLikeEquiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))))) (Subgroup.opposite.{u1} G _inst_1) H))) G (Submonoid.instSMulSubtypeMemSubmonoidInstMembershipInstSetLikeSubmonoid.{u1, u1} (MulOpposite.{u1} G) G (Monoid.toMulOneClass.{u1} (MulOpposite.{u1} G) (DivInvMonoid.toMonoid.{u1} (MulOpposite.{u1} G) (Group.toDivInvMonoid.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)))) (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Subgroup.toSubmonoid.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) (Subgroup.{u1} G _inst_1) (fun (a : Subgroup.{u1} G _inst_1) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subgroup.{u1} G _inst_1) => Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) a) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))) (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1)) (Equiv.instEquivLikeEquiv.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Subgroup.{u1} (MulOpposite.{u1} G) (MulOpposite.instGroupMulOpposite.{u1} G _inst_1))))) (Subgroup.opposite.{u1} G _inst_1) H)))) h x))
Case conversion may be inaccurate. Consider using '#align subgroup.smul_opposite_mul Subgroup.smul_opposite_mulₓ'. -/
@[to_additive]
theorem smul_opposite_mul {H : Subgroup G} (x g : G) (h : H.opposite) : h • (g * x) = g * h • x :=
  by
  cases h
  simp [(· • ·), mul_assoc]
#align subgroup.smul_opposite_mul Subgroup.smul_opposite_mul
#align add_subgroup.vadd_opposite_add AddSubgroup.vadd_opposite_add

end Subgroup

