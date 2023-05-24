/-
Copyright (c) 2022 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang

! This file was ported from Lean 3 source module linear_algebra.affine_space.pointwise
! leanprover-community/mathlib commit 31ca6f9cf5f90a6206092cd7f84b359dcb6d52e0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.AffineSpace.AffineSubspace

/-! # Pointwise instances on `affine_subspace`s

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides the additive action `affine_subspace.pointwise_add_action` in the
`pointwise` locale.

-/


open Affine Pointwise

open Set

namespace AffineSubspace

variable {k : Type _} [Ring k]

variable {V P V₁ P₁ V₂ P₂ : Type _}

variable [AddCommGroup V] [Module k V] [affine_space V P]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

include V

#print AffineSubspace.pointwiseAddAction /-
/-- The additive action on an affine subspace corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwiseAddAction : AddAction V (AffineSubspace k P)
    where
  vadd x S := S.map (AffineEquiv.constVAdd k P x)
  zero_vadd p := ((congr_arg fun f => p.map f) <| AffineMap.ext <| zero_vadd _).trans p.map_id
  add_vadd x y p :=
    ((congr_arg fun f => p.map f) <| AffineMap.ext <| add_vadd _ _).trans (p.map_map _ _).symm
#align affine_subspace.pointwise_add_action AffineSubspace.pointwiseAddAction
-/

scoped[Pointwise] attribute [instance] AffineSubspace.pointwiseAddAction

open Pointwise

/- warning: affine_subspace.coe_pointwise_vadd -> AffineSubspace.coe_pointwise_vadd is a dubious translation:
lean 3 declaration is
  forall {k : Type.{u1}} [_inst_1 : Ring.{u1} k] {V : Type.{u2}} {P : Type.{u3}} [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} k V (Ring.toSemiring.{u1} k _inst_1) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] (v : V) (s : AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4), Eq.{succ u3} (Set.{u3} P) ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (Set.{u3} P) (HasLiftT.mk.{succ u3, succ u3} (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (Set.{u3} P) (CoeTCₓ.coe.{succ u3, succ u3} (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (Set.{u3} P) (SetLike.Set.hasCoeT.{u3, u3} (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4)))) (VAdd.vadd.{u2, u3} V (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (AddAction.toHasVadd.{u2, u3} V (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AffineSubspace.pointwiseAddAction.{u1, u2, u3} k _inst_1 V P _inst_2 _inst_3 _inst_4)) v s)) (VAdd.vadd.{u2, u3} V (Set.{u3} P) (Set.vaddSet.{u2, u3} V P (AddAction.toHasVadd.{u2, u3} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AddTorsor.toAddAction.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2) _inst_4))) v ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (Set.{u3} P) (HasLiftT.mk.{succ u3, succ u3} (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (Set.{u3} P) (CoeTCₓ.coe.{succ u3, succ u3} (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (Set.{u3} P) (SetLike.Set.hasCoeT.{u3, u3} (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4)))) s))
but is expected to have type
  forall {k : Type.{u3}} [_inst_1 : Ring.{u3} k] {V : Type.{u2}} {P : Type.{u1}} [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} k V (Ring.toSemiring.{u3} k _inst_1) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] (v : V) (s : AffineSubspace.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4), Eq.{succ u1} (Set.{u1} P) (SetLike.coe.{u1, u1} (AffineSubspace.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4) (HVAdd.hVAdd.{u2, u1, u1} V (AffineSubspace.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4) (AffineSubspace.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4) (instHVAdd.{u2, u1} V (AffineSubspace.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4) (AddAction.toVAdd.{u2, u1} V (AffineSubspace.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4) (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AffineSubspace.pointwiseAddAction.{u3, u2, u1} k _inst_1 V P _inst_2 _inst_3 _inst_4))) v s)) (HVAdd.hVAdd.{u2, u1, u1} V (Set.{u1} P) (Set.{u1} P) (instHVAdd.{u2, u1} V (Set.{u1} P) (Set.vaddSet.{u2, u1} V P (AddAction.toVAdd.{u2, u1} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AddTorsor.toAddAction.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2) _inst_4)))) v (SetLike.coe.{u1, u1} (AffineSubspace.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4) s))
Case conversion may be inaccurate. Consider using '#align affine_subspace.coe_pointwise_vadd AffineSubspace.coe_pointwise_vaddₓ'. -/
@[simp]
theorem coe_pointwise_vadd (v : V) (s : AffineSubspace k P) :
    ((v +ᵥ s : AffineSubspace k P) : Set P) = v +ᵥ s :=
  rfl
#align affine_subspace.coe_pointwise_vadd AffineSubspace.coe_pointwise_vadd

/- warning: affine_subspace.vadd_mem_pointwise_vadd_iff -> AffineSubspace.vadd_mem_pointwise_vadd_iff is a dubious translation:
lean 3 declaration is
  forall {k : Type.{u1}} [_inst_1 : Ring.{u1} k] {V : Type.{u2}} {P : Type.{u3}} [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} k V (Ring.toSemiring.{u1} k _inst_1) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {v : V} {s : AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4} {p : P}, Iff (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4)) (VAdd.vadd.{u2, u3} V P (AddAction.toHasVadd.{u2, u3} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AddTorsor.toAddAction.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2) _inst_4)) v p) (VAdd.vadd.{u2, u3} V (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (AddAction.toHasVadd.{u2, u3} V (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AffineSubspace.pointwiseAddAction.{u1, u2, u3} k _inst_1 V P _inst_2 _inst_3 _inst_4)) v s)) (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4)) p s)
but is expected to have type
  forall {k : Type.{u3}} [_inst_1 : Ring.{u3} k] {V : Type.{u2}} {P : Type.{u1}} [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} k V (Ring.toSemiring.{u3} k _inst_1) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {v : V} {s : AffineSubspace.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4} {p : P}, Iff (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4)) (HVAdd.hVAdd.{u2, u1, u1} V P P (instHVAdd.{u2, u1} V P (AddAction.toVAdd.{u2, u1} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AddTorsor.toAddAction.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2) _inst_4))) v p) (HVAdd.hVAdd.{u2, u1, u1} V (AffineSubspace.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4) (AffineSubspace.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4) (instHVAdd.{u2, u1} V (AffineSubspace.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4) (AddAction.toVAdd.{u2, u1} V (AffineSubspace.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4) (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AffineSubspace.pointwiseAddAction.{u3, u2, u1} k _inst_1 V P _inst_2 _inst_3 _inst_4))) v s)) (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4)) p s)
Case conversion may be inaccurate. Consider using '#align affine_subspace.vadd_mem_pointwise_vadd_iff AffineSubspace.vadd_mem_pointwise_vadd_iffₓ'. -/
theorem vadd_mem_pointwise_vadd_iff {v : V} {s : AffineSubspace k P} {p : P} :
    v +ᵥ p ∈ v +ᵥ s ↔ p ∈ s :=
  vadd_mem_vadd_set_iff
#align affine_subspace.vadd_mem_pointwise_vadd_iff AffineSubspace.vadd_mem_pointwise_vadd_iff

/- warning: affine_subspace.pointwise_vadd_bot -> AffineSubspace.pointwise_vadd_bot is a dubious translation:
lean 3 declaration is
  forall {k : Type.{u1}} [_inst_1 : Ring.{u1} k] {V : Type.{u2}} {P : Type.{u3}} [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} k V (Ring.toSemiring.{u1} k _inst_1) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] (v : V), Eq.{succ u3} (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (VAdd.vadd.{u2, u3} V (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (AddAction.toHasVadd.{u2, u3} V (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AffineSubspace.pointwiseAddAction.{u1, u2, u3} k _inst_1 V P _inst_2 _inst_3 _inst_4)) v (Bot.bot.{u3} (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (CompleteLattice.toHasBot.{u3} (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (AffineSubspace.completeLattice.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4)))) (Bot.bot.{u3} (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (CompleteLattice.toHasBot.{u3} (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (AffineSubspace.completeLattice.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4)))
but is expected to have type
  forall {k : Type.{u2}} [_inst_1 : Ring.{u2} k] {V : Type.{u1}} {P : Type.{u3}} [_inst_2 : AddCommGroup.{u1} V] [_inst_3 : Module.{u2, u1} k V (Ring.toSemiring.{u2} k _inst_1) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] [_inst_4 : AddTorsor.{u1, u3} V P (AddCommGroup.toAddGroup.{u1} V _inst_2)] (v : V), Eq.{succ u3} (AffineSubspace.{u2, u1, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (HVAdd.hVAdd.{u1, u3, u3} V (AffineSubspace.{u2, u1, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (AffineSubspace.{u2, u1, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (instHVAdd.{u1, u3} V (AffineSubspace.{u2, u1, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (AddAction.toVAdd.{u1, u3} V (AffineSubspace.{u2, u1, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (AddCommGroup.toAddGroup.{u1} V _inst_2))) (AffineSubspace.pointwiseAddAction.{u2, u1, u3} k _inst_1 V P _inst_2 _inst_3 _inst_4))) v (Bot.bot.{u3} (AffineSubspace.{u2, u1, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (CompleteLattice.toBot.{u3} (AffineSubspace.{u2, u1, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (AffineSubspace.instCompleteLatticeAffineSubspace.{u2, u1, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4)))) (Bot.bot.{u3} (AffineSubspace.{u2, u1, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (CompleteLattice.toBot.{u3} (AffineSubspace.{u2, u1, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (AffineSubspace.instCompleteLatticeAffineSubspace.{u2, u1, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4)))
Case conversion may be inaccurate. Consider using '#align affine_subspace.pointwise_vadd_bot AffineSubspace.pointwise_vadd_botₓ'. -/
theorem pointwise_vadd_bot (v : V) : v +ᵥ (⊥ : AffineSubspace k P) = ⊥ := by simp [SetLike.ext'_iff]
#align affine_subspace.pointwise_vadd_bot AffineSubspace.pointwise_vadd_bot

/- warning: affine_subspace.pointwise_vadd_direction -> AffineSubspace.pointwise_vadd_direction is a dubious translation:
lean 3 declaration is
  forall {k : Type.{u1}} [_inst_1 : Ring.{u1} k] {V : Type.{u2}} {P : Type.{u3}} [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} k V (Ring.toSemiring.{u1} k _inst_1) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] (v : V) (s : AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4), Eq.{succ u2} (Submodule.{u1, u2} k V (Ring.toSemiring.{u1} k _inst_1) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) (AffineSubspace.direction.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4 (VAdd.vadd.{u2, u3} V (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (AddAction.toHasVadd.{u2, u3} V (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AffineSubspace.pointwiseAddAction.{u1, u2, u3} k _inst_1 V P _inst_2 _inst_3 _inst_4)) v s)) (AffineSubspace.direction.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4 s)
but is expected to have type
  forall {k : Type.{u3}} [_inst_1 : Ring.{u3} k] {V : Type.{u2}} {P : Type.{u1}} [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} k V (Ring.toSemiring.{u3} k _inst_1) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] (v : V) (s : AffineSubspace.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4), Eq.{succ u2} (Submodule.{u3, u2} k V (Ring.toSemiring.{u3} k _inst_1) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) (AffineSubspace.direction.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4 (HVAdd.hVAdd.{u2, u1, u1} V (AffineSubspace.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4) (AffineSubspace.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4) (instHVAdd.{u2, u1} V (AffineSubspace.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4) (AddAction.toVAdd.{u2, u1} V (AffineSubspace.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4) (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AffineSubspace.pointwiseAddAction.{u3, u2, u1} k _inst_1 V P _inst_2 _inst_3 _inst_4))) v s)) (AffineSubspace.direction.{u3, u2, u1} k V P _inst_1 _inst_2 _inst_3 _inst_4 s)
Case conversion may be inaccurate. Consider using '#align affine_subspace.pointwise_vadd_direction AffineSubspace.pointwise_vadd_directionₓ'. -/
theorem pointwise_vadd_direction (v : V) (s : AffineSubspace k P) :
    (v +ᵥ s).direction = s.direction := by
  unfold VAdd.vadd
  rw [map_direction]
  exact Submodule.map_id _
#align affine_subspace.pointwise_vadd_direction AffineSubspace.pointwise_vadd_direction

/- warning: affine_subspace.pointwise_vadd_span -> AffineSubspace.pointwise_vadd_span is a dubious translation:
lean 3 declaration is
  forall {k : Type.{u1}} [_inst_1 : Ring.{u1} k] {V : Type.{u2}} {P : Type.{u3}} [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} k V (Ring.toSemiring.{u1} k _inst_1) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] (v : V) (s : Set.{u3} P), Eq.{succ u3} (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (VAdd.vadd.{u2, u3} V (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (AddAction.toHasVadd.{u2, u3} V (AffineSubspace.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AffineSubspace.pointwiseAddAction.{u1, u2, u3} k _inst_1 V P _inst_2 _inst_3 _inst_4)) v (affineSpan.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4 s)) (affineSpan.{u1, u2, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4 (VAdd.vadd.{u2, u3} V (Set.{u3} P) (Set.vaddSet.{u2, u3} V P (AddAction.toHasVadd.{u2, u3} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AddTorsor.toAddAction.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2) _inst_4))) v s))
but is expected to have type
  forall {k : Type.{u2}} [_inst_1 : Ring.{u2} k] {V : Type.{u1}} {P : Type.{u3}} [_inst_2 : AddCommGroup.{u1} V] [_inst_3 : Module.{u2, u1} k V (Ring.toSemiring.{u2} k _inst_1) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] [_inst_4 : AddTorsor.{u1, u3} V P (AddCommGroup.toAddGroup.{u1} V _inst_2)] (v : V) (s : Set.{u3} P), Eq.{succ u3} (AffineSubspace.{u2, u1, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (HVAdd.hVAdd.{u1, u3, u3} V (AffineSubspace.{u2, u1, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (AffineSubspace.{u2, u1, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (instHVAdd.{u1, u3} V (AffineSubspace.{u2, u1, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (AddAction.toVAdd.{u1, u3} V (AffineSubspace.{u2, u1, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4) (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (AddCommGroup.toAddGroup.{u1} V _inst_2))) (AffineSubspace.pointwiseAddAction.{u2, u1, u3} k _inst_1 V P _inst_2 _inst_3 _inst_4))) v (affineSpan.{u2, u1, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4 s)) (affineSpan.{u2, u1, u3} k V P _inst_1 _inst_2 _inst_3 _inst_4 (HVAdd.hVAdd.{u1, u3, u3} V (Set.{u3} P) (Set.{u3} P) (instHVAdd.{u1, u3} V (Set.{u3} P) (Set.vaddSet.{u1, u3} V P (AddAction.toVAdd.{u1, u3} V P (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (AddCommGroup.toAddGroup.{u1} V _inst_2))) (AddTorsor.toAddAction.{u1, u3} V P (AddCommGroup.toAddGroup.{u1} V _inst_2) _inst_4)))) v s))
Case conversion may be inaccurate. Consider using '#align affine_subspace.pointwise_vadd_span AffineSubspace.pointwise_vadd_spanₓ'. -/
theorem pointwise_vadd_span (v : V) (s : Set P) : v +ᵥ affineSpan k s = affineSpan k (v +ᵥ s) :=
  map_span _ s
#align affine_subspace.pointwise_vadd_span AffineSubspace.pointwise_vadd_span

omit V

include V₁ V₂

/- warning: affine_subspace.map_pointwise_vadd -> AffineSubspace.map_pointwise_vadd is a dubious translation:
lean 3 declaration is
  forall {k : Type.{u1}} [_inst_1 : Ring.{u1} k] {V₁ : Type.{u2}} {P₁ : Type.{u3}} {V₂ : Type.{u4}} {P₂ : Type.{u5}} [_inst_5 : AddCommGroup.{u2} V₁] [_inst_6 : Module.{u1, u2} k V₁ (Ring.toSemiring.{u1} k _inst_1) (AddCommGroup.toAddCommMonoid.{u2} V₁ _inst_5)] [_inst_7 : AddTorsor.{u2, u3} V₁ P₁ (AddCommGroup.toAddGroup.{u2} V₁ _inst_5)] [_inst_8 : AddCommGroup.{u4} V₂] [_inst_9 : Module.{u1, u4} k V₂ (Ring.toSemiring.{u1} k _inst_1) (AddCommGroup.toAddCommMonoid.{u4} V₂ _inst_8)] [_inst_10 : AddTorsor.{u4, u5} V₂ P₂ (AddCommGroup.toAddGroup.{u4} V₂ _inst_8)] (f : AffineMap.{u1, u2, u3, u4, u5} k V₁ P₁ V₂ P₂ _inst_1 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10) (v : V₁) (s : AffineSubspace.{u1, u2, u3} k V₁ P₁ _inst_1 _inst_5 _inst_6 _inst_7), Eq.{succ u5} (AffineSubspace.{u1, u4, u5} k V₂ P₂ _inst_1 _inst_8 _inst_9 _inst_10) (AffineSubspace.map.{u1, u2, u3, u4, u5} k V₁ P₁ V₂ P₂ _inst_1 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10 f (VAdd.vadd.{u2, u3} V₁ (AffineSubspace.{u1, u2, u3} k V₁ P₁ _inst_1 _inst_5 _inst_6 _inst_7) (AddAction.toHasVadd.{u2, u3} V₁ (AffineSubspace.{u1, u2, u3} k V₁ P₁ _inst_1 _inst_5 _inst_6 _inst_7) (SubNegMonoid.toAddMonoid.{u2} V₁ (AddGroup.toSubNegMonoid.{u2} V₁ (AddCommGroup.toAddGroup.{u2} V₁ _inst_5))) (AffineSubspace.pointwiseAddAction.{u1, u2, u3} k _inst_1 V₁ P₁ _inst_5 _inst_6 _inst_7)) v s)) (VAdd.vadd.{u4, u5} V₂ (AffineSubspace.{u1, u4, u5} k V₂ P₂ _inst_1 _inst_8 _inst_9 _inst_10) (AddAction.toHasVadd.{u4, u5} V₂ (AffineSubspace.{u1, u4, u5} k V₂ P₂ _inst_1 _inst_8 _inst_9 _inst_10) (SubNegMonoid.toAddMonoid.{u4} V₂ (AddGroup.toSubNegMonoid.{u4} V₂ (AddCommGroup.toAddGroup.{u4} V₂ _inst_8))) (AffineSubspace.pointwiseAddAction.{u1, u4, u5} k _inst_1 V₂ P₂ _inst_8 _inst_9 _inst_10)) (coeFn.{max (succ u2) (succ u4), max (succ u2) (succ u4)} (LinearMap.{u1, u1, u2, u4} k k (Ring.toSemiring.{u1} k _inst_1) (Ring.toSemiring.{u1} k _inst_1) (RingHom.id.{u1} k (Semiring.toNonAssocSemiring.{u1} k (Ring.toSemiring.{u1} k _inst_1))) V₁ V₂ (AddCommGroup.toAddCommMonoid.{u2} V₁ _inst_5) (AddCommGroup.toAddCommMonoid.{u4} V₂ _inst_8) _inst_6 _inst_9) (fun (_x : LinearMap.{u1, u1, u2, u4} k k (Ring.toSemiring.{u1} k _inst_1) (Ring.toSemiring.{u1} k _inst_1) (RingHom.id.{u1} k (Semiring.toNonAssocSemiring.{u1} k (Ring.toSemiring.{u1} k _inst_1))) V₁ V₂ (AddCommGroup.toAddCommMonoid.{u2} V₁ _inst_5) (AddCommGroup.toAddCommMonoid.{u4} V₂ _inst_8) _inst_6 _inst_9) => V₁ -> V₂) (LinearMap.hasCoeToFun.{u1, u1, u2, u4} k k V₁ V₂ (Ring.toSemiring.{u1} k _inst_1) (Ring.toSemiring.{u1} k _inst_1) (AddCommGroup.toAddCommMonoid.{u2} V₁ _inst_5) (AddCommGroup.toAddCommMonoid.{u4} V₂ _inst_8) _inst_6 _inst_9 (RingHom.id.{u1} k (Semiring.toNonAssocSemiring.{u1} k (Ring.toSemiring.{u1} k _inst_1)))) (AffineMap.linear.{u1, u2, u3, u4, u5} k V₁ P₁ V₂ P₂ _inst_1 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10 f) v) (AffineSubspace.map.{u1, u2, u3, u4, u5} k V₁ P₁ V₂ P₂ _inst_1 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10 f s))
but is expected to have type
  forall {k : Type.{u5}} [_inst_1 : Ring.{u5} k] {V₁ : Type.{u4}} {P₁ : Type.{u3}} {V₂ : Type.{u2}} {P₂ : Type.{u1}} [_inst_5 : AddCommGroup.{u4} V₁] [_inst_6 : Module.{u5, u4} k V₁ (Ring.toSemiring.{u5} k _inst_1) (AddCommGroup.toAddCommMonoid.{u4} V₁ _inst_5)] [_inst_7 : AddTorsor.{u4, u3} V₁ P₁ (AddCommGroup.toAddGroup.{u4} V₁ _inst_5)] [_inst_8 : AddCommGroup.{u2} V₂] [_inst_9 : Module.{u5, u2} k V₂ (Ring.toSemiring.{u5} k _inst_1) (AddCommGroup.toAddCommMonoid.{u2} V₂ _inst_8)] [_inst_10 : AddTorsor.{u2, u1} V₂ P₂ (AddCommGroup.toAddGroup.{u2} V₂ _inst_8)] (f : AffineMap.{u5, u4, u3, u2, u1} k V₁ P₁ V₂ P₂ _inst_1 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10) (v : V₁) (s : AffineSubspace.{u5, u4, u3} k V₁ P₁ _inst_1 _inst_5 _inst_6 _inst_7), Eq.{succ u1} (AffineSubspace.{u5, u2, u1} k V₂ P₂ _inst_1 _inst_8 _inst_9 _inst_10) (AffineSubspace.map.{u5, u4, u3, u2, u1} k V₁ P₁ V₂ P₂ _inst_1 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10 f (HVAdd.hVAdd.{u4, u3, u3} V₁ (AffineSubspace.{u5, u4, u3} k V₁ P₁ _inst_1 _inst_5 _inst_6 _inst_7) (AffineSubspace.{u5, u4, u3} k V₁ P₁ _inst_1 _inst_5 _inst_6 _inst_7) (instHVAdd.{u4, u3} V₁ (AffineSubspace.{u5, u4, u3} k V₁ P₁ _inst_1 _inst_5 _inst_6 _inst_7) (AddAction.toVAdd.{u4, u3} V₁ (AffineSubspace.{u5, u4, u3} k V₁ P₁ _inst_1 _inst_5 _inst_6 _inst_7) (SubNegMonoid.toAddMonoid.{u4} V₁ (AddGroup.toSubNegMonoid.{u4} V₁ (AddCommGroup.toAddGroup.{u4} V₁ _inst_5))) (AffineSubspace.pointwiseAddAction.{u5, u4, u3} k _inst_1 V₁ P₁ _inst_5 _inst_6 _inst_7))) v s)) (HVAdd.hVAdd.{u2, u1, u1} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : V₁) => V₂) v) (AffineSubspace.{u5, u2, u1} k V₂ P₂ _inst_1 _inst_8 _inst_9 _inst_10) (AffineSubspace.{u5, u2, u1} k V₂ P₂ _inst_1 _inst_8 _inst_9 _inst_10) (instHVAdd.{u2, u1} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : V₁) => V₂) v) (AffineSubspace.{u5, u2, u1} k V₂ P₂ _inst_1 _inst_8 _inst_9 _inst_10) (AddAction.toVAdd.{u2, u1} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : V₁) => V₂) v) (AffineSubspace.{u5, u2, u1} k V₂ P₂ _inst_1 _inst_8 _inst_9 _inst_10) (SubNegMonoid.toAddMonoid.{u2} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : V₁) => V₂) v) (AddGroup.toSubNegMonoid.{u2} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : V₁) => V₂) v) (AddCommGroup.toAddGroup.{u2} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : V₁) => V₂) v) _inst_8))) (AffineSubspace.pointwiseAddAction.{u5, u2, u1} k _inst_1 ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : V₁) => V₂) v) P₂ _inst_8 _inst_9 _inst_10))) (FunLike.coe.{max (succ u4) (succ u2), succ u4, succ u2} (LinearMap.{u5, u5, u4, u2} k k (Ring.toSemiring.{u5} k _inst_1) (Ring.toSemiring.{u5} k _inst_1) (RingHom.id.{u5} k (Semiring.toNonAssocSemiring.{u5} k (Ring.toSemiring.{u5} k _inst_1))) V₁ V₂ (AddCommGroup.toAddCommMonoid.{u4} V₁ _inst_5) (AddCommGroup.toAddCommMonoid.{u2} V₂ _inst_8) _inst_6 _inst_9) V₁ (fun (_x : V₁) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : V₁) => V₂) _x) (LinearMap.instFunLikeLinearMap.{u5, u5, u4, u2} k k V₁ V₂ (Ring.toSemiring.{u5} k _inst_1) (Ring.toSemiring.{u5} k _inst_1) (AddCommGroup.toAddCommMonoid.{u4} V₁ _inst_5) (AddCommGroup.toAddCommMonoid.{u2} V₂ _inst_8) _inst_6 _inst_9 (RingHom.id.{u5} k (Semiring.toNonAssocSemiring.{u5} k (Ring.toSemiring.{u5} k _inst_1)))) (AffineMap.linear.{u5, u4, u3, u2, u1} k V₁ P₁ V₂ P₂ _inst_1 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10 f) v) (AffineSubspace.map.{u5, u4, u3, u2, u1} k V₁ P₁ V₂ P₂ _inst_1 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10 f s))
Case conversion may be inaccurate. Consider using '#align affine_subspace.map_pointwise_vadd AffineSubspace.map_pointwise_vaddₓ'. -/
theorem map_pointwise_vadd (f : P₁ →ᵃ[k] P₂) (v : V₁) (s : AffineSubspace k P₁) :
    (v +ᵥ s).map f = f.linear v +ᵥ s.map f :=
  by
  unfold VAdd.vadd
  rw [map_map, map_map]
  congr 1
  ext
  exact f.map_vadd _ _
#align affine_subspace.map_pointwise_vadd AffineSubspace.map_pointwise_vadd

end AffineSubspace

