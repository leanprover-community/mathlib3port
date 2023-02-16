/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module ring_theory.subsemiring.pointwise
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GroupRingAction.Basic
import Mathbin.RingTheory.Subsemiring.Basic
import Mathbin.GroupTheory.Submonoid.Pointwise
import Mathbin.Data.Set.Pointwise.Basic

/-! # Pointwise instances on `subsemiring`s

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides the action `subsemiring.pointwise_mul_action` which matches the action of
`mul_action_set`.

This actions is available in the `pointwise` locale.

## Implementation notes

This file is almost identical to `group_theory/submonoid/pointwise.lean`. Where possible, try to
keep them in sync.
-/


open Set

variable {M R : Type _}

namespace Subsemiring

section Monoid

variable [Monoid M] [Semiring R] [MulSemiringAction M R]

#print Subsemiring.pointwiseMulAction /-
/-- The action on a subsemiring corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwiseMulAction : MulAction M (Subsemiring R)
    where
  smul a S := S.map (MulSemiringAction.toRingHom _ _ a)
  one_smul S := (congr_arg (fun f => S.map f) (RingHom.ext <| one_smul M)).trans S.map_id
  mul_smul a₁ a₂ S :=
    (congr_arg (fun f => S.map f) (RingHom.ext <| mul_smul _ _)).trans (S.map_map _ _).symm
#align subsemiring.pointwise_mul_action Subsemiring.pointwiseMulAction
-/

scoped[Pointwise] attribute [instance] Subsemiring.pointwiseMulAction

open Pointwise

#print Subsemiring.pointwise_smul_def /-
theorem pointwise_smul_def {a : M} (S : Subsemiring R) :
    a • S = S.map (MulSemiringAction.toRingHom _ _ a) :=
  rfl
#align subsemiring.pointwise_smul_def Subsemiring.pointwise_smul_def
-/

/- warning: subsemiring.coe_pointwise_smul -> Subsemiring.coe_pointwise_smul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {R : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Semiring.{u2} R] [_inst_3 : MulSemiringAction.{u1, u2} M R _inst_1 _inst_2] (m : M) (S : Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)), Eq.{succ u2} (Set.{u2} R) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (Set.{u2} R) (HasLiftT.mk.{succ u2, succ u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (Set.{u2} R) (CoeTCₓ.coe.{succ u2, succ u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (Set.{u2} R) (SetLike.Set.hasCoeT.{u2, u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) R (Subsemiring.setLike.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))))) (SMul.smul.{u1, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (MulAction.toHasSmul.{u1, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) _inst_1 (Subsemiring.pointwiseMulAction.{u1, u2} M R _inst_1 _inst_2 _inst_3)) m S)) (SMul.smul.{u1, u2} M (Set.{u2} R) (Set.smulSet.{u1, u2} M R (SMulZeroClass.toHasSmul.{u1, u2} M R (AddZeroClass.toHasZero.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)))))) (DistribSMul.toSmulZeroClass.{u1, u2} M R (AddMonoid.toAddZeroClass.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))))) (DistribMulAction.toDistribSMul.{u1, u2} M R _inst_1 (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)))) (MulSemiringAction.toDistribMulAction.{u1, u2} M R _inst_1 _inst_2 _inst_3))))) m ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (Set.{u2} R) (HasLiftT.mk.{succ u2, succ u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (Set.{u2} R) (CoeTCₓ.coe.{succ u2, succ u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (Set.{u2} R) (SetLike.Set.hasCoeT.{u2, u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) R (Subsemiring.setLike.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))))) S))
but is expected to have type
  forall {M : Type.{u1}} {R : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Semiring.{u2} R] [_inst_3 : MulSemiringAction.{u1, u2} M R _inst_1 _inst_2] (m : M) (S : Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)), Eq.{succ u2} (Set.{u2} R) (SetLike.coe.{u2, u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) R (Subsemiring.instSetLikeSubsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (HSMul.hSMul.{u1, u2, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (instHSMul.{u1, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (MulAction.toSMul.{u1, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) _inst_1 (Subsemiring.pointwiseMulAction.{u1, u2} M R _inst_1 _inst_2 _inst_3))) m S)) (HSMul.hSMul.{u1, u2, u2} M (Set.{u2} R) (Set.{u2} R) (instHSMul.{u1, u2} M (Set.{u2} R) (Set.smulSet.{u1, u2} M R (SMulZeroClass.toSMul.{u1, u2} M R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_2)) (DistribSMul.toSMulZeroClass.{u1, u2} M R (AddMonoid.toAddZeroClass.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))))) (DistribMulAction.toDistribSMul.{u1, u2} M R _inst_1 (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)))) (MulSemiringAction.toDistribMulAction.{u1, u2} M R _inst_1 _inst_2 _inst_3)))))) m (SetLike.coe.{u2, u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) R (Subsemiring.instSetLikeSubsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) S))
Case conversion may be inaccurate. Consider using '#align subsemiring.coe_pointwise_smul Subsemiring.coe_pointwise_smulₓ'. -/
@[simp]
theorem coe_pointwise_smul (m : M) (S : Subsemiring R) : ↑(m • S) = m • (S : Set R) :=
  rfl
#align subsemiring.coe_pointwise_smul Subsemiring.coe_pointwise_smul

#print Subsemiring.pointwise_smul_toAddSubmonoid /-
@[simp]
theorem pointwise_smul_toAddSubmonoid (m : M) (S : Subsemiring R) :
    (m • S).toAddSubmonoid = m • S.toAddSubmonoid :=
  rfl
#align subsemiring.pointwise_smul_to_add_submonoid Subsemiring.pointwise_smul_toAddSubmonoid
-/

/- warning: subsemiring.smul_mem_pointwise_smul -> Subsemiring.smul_mem_pointwise_smul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {R : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Semiring.{u2} R] [_inst_3 : MulSemiringAction.{u1, u2} M R _inst_1 _inst_2] (m : M) (r : R) (S : Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)), (Membership.Mem.{u2, u2} R (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (SetLike.hasMem.{u2, u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) R (Subsemiring.setLike.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))) r S) -> (Membership.Mem.{u2, u2} R (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (SetLike.hasMem.{u2, u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) R (Subsemiring.setLike.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))) (SMul.smul.{u1, u2} M R (SMulZeroClass.toHasSmul.{u1, u2} M R (AddZeroClass.toHasZero.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)))))) (DistribSMul.toSmulZeroClass.{u1, u2} M R (AddMonoid.toAddZeroClass.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))))) (DistribMulAction.toDistribSMul.{u1, u2} M R _inst_1 (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)))) (MulSemiringAction.toDistribMulAction.{u1, u2} M R _inst_1 _inst_2 _inst_3)))) m r) (SMul.smul.{u1, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (MulAction.toHasSmul.{u1, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) _inst_1 (Subsemiring.pointwiseMulAction.{u1, u2} M R _inst_1 _inst_2 _inst_3)) m S))
but is expected to have type
  forall {M : Type.{u1}} {R : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Semiring.{u2} R] [_inst_3 : MulSemiringAction.{u1, u2} M R _inst_1 _inst_2] (m : M) (r : R) (S : Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)), (Membership.mem.{u2, u2} R (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (SetLike.instMembership.{u2, u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) R (Subsemiring.instSetLikeSubsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))) r S) -> (Membership.mem.{u2, u2} R (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (SetLike.instMembership.{u2, u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) R (Subsemiring.instSetLikeSubsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))) (HSMul.hSMul.{u1, u2, u2} M R R (instHSMul.{u1, u2} M R (SMulZeroClass.toSMul.{u1, u2} M R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_2)) (DistribSMul.toSMulZeroClass.{u1, u2} M R (AddMonoid.toAddZeroClass.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))))) (DistribMulAction.toDistribSMul.{u1, u2} M R _inst_1 (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)))) (MulSemiringAction.toDistribMulAction.{u1, u2} M R _inst_1 _inst_2 _inst_3))))) m r) (HSMul.hSMul.{u1, u2, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (instHSMul.{u1, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (MulAction.toSMul.{u1, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) _inst_1 (Subsemiring.pointwiseMulAction.{u1, u2} M R _inst_1 _inst_2 _inst_3))) m S))
Case conversion may be inaccurate. Consider using '#align subsemiring.smul_mem_pointwise_smul Subsemiring.smul_mem_pointwise_smulₓ'. -/
theorem smul_mem_pointwise_smul (m : M) (r : R) (S : Subsemiring R) : r ∈ S → m • r ∈ m • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ m • (S : Set R))
#align subsemiring.smul_mem_pointwise_smul Subsemiring.smul_mem_pointwise_smul

/- warning: subsemiring.mem_smul_pointwise_iff_exists -> Subsemiring.mem_smul_pointwise_iff_exists is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {R : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Semiring.{u2} R] [_inst_3 : MulSemiringAction.{u1, u2} M R _inst_1 _inst_2] (m : M) (r : R) (S : Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)), Iff (Membership.Mem.{u2, u2} R (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (SetLike.hasMem.{u2, u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) R (Subsemiring.setLike.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))) r (SMul.smul.{u1, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (MulAction.toHasSmul.{u1, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) _inst_1 (Subsemiring.pointwiseMulAction.{u1, u2} M R _inst_1 _inst_2 _inst_3)) m S)) (Exists.{succ u2} R (fun (s : R) => And (Membership.Mem.{u2, u2} R (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (SetLike.hasMem.{u2, u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) R (Subsemiring.setLike.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))) s S) (Eq.{succ u2} R (SMul.smul.{u1, u2} M R (SMulZeroClass.toHasSmul.{u1, u2} M R (AddZeroClass.toHasZero.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)))))) (DistribSMul.toSmulZeroClass.{u1, u2} M R (AddMonoid.toAddZeroClass.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))))) (DistribMulAction.toDistribSMul.{u1, u2} M R _inst_1 (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)))) (MulSemiringAction.toDistribMulAction.{u1, u2} M R _inst_1 _inst_2 _inst_3)))) m s) r)))
but is expected to have type
  forall {M : Type.{u1}} {R : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Semiring.{u2} R] [_inst_3 : MulSemiringAction.{u1, u2} M R _inst_1 _inst_2] (m : M) (r : R) (S : Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)), Iff (Membership.mem.{u2, u2} R (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (SetLike.instMembership.{u2, u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) R (Subsemiring.instSetLikeSubsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))) r (HSMul.hSMul.{u1, u2, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (instHSMul.{u1, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (MulAction.toSMul.{u1, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) _inst_1 (Subsemiring.pointwiseMulAction.{u1, u2} M R _inst_1 _inst_2 _inst_3))) m S)) (Exists.{succ u2} R (fun (s : R) => And (Membership.mem.{u2, u2} R (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (SetLike.instMembership.{u2, u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) R (Subsemiring.instSetLikeSubsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))) s S) (Eq.{succ u2} R (HSMul.hSMul.{u1, u2, u2} M R R (instHSMul.{u1, u2} M R (SMulZeroClass.toSMul.{u1, u2} M R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_2)) (DistribSMul.toSMulZeroClass.{u1, u2} M R (AddMonoid.toAddZeroClass.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))))) (DistribMulAction.toDistribSMul.{u1, u2} M R _inst_1 (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)))) (MulSemiringAction.toDistribMulAction.{u1, u2} M R _inst_1 _inst_2 _inst_3))))) m s) r)))
Case conversion may be inaccurate. Consider using '#align subsemiring.mem_smul_pointwise_iff_exists Subsemiring.mem_smul_pointwise_iff_existsₓ'. -/
theorem mem_smul_pointwise_iff_exists (m : M) (r : R) (S : Subsemiring R) :
    r ∈ m • S ↔ ∃ s : R, s ∈ S ∧ m • s = r :=
  (Set.mem_smul_set : r ∈ m • (S : Set R) ↔ _)
#align subsemiring.mem_smul_pointwise_iff_exists Subsemiring.mem_smul_pointwise_iff_exists

#print Subsemiring.smul_bot /-
@[simp]
theorem smul_bot (a : M) : a • (⊥ : Subsemiring R) = ⊥ :=
  map_bot _
#align subsemiring.smul_bot Subsemiring.smul_bot
-/

/- warning: subsemiring.smul_sup -> Subsemiring.smul_sup is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {R : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Semiring.{u2} R] [_inst_3 : MulSemiringAction.{u1, u2} M R _inst_1 _inst_2] (a : M) (S : Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (T : Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)), Eq.{succ u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (SMul.smul.{u1, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (MulAction.toHasSmul.{u1, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) _inst_1 (Subsemiring.pointwiseMulAction.{u1, u2} M R _inst_1 _inst_2 _inst_3)) a (HasSup.sup.{u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (SemilatticeSup.toHasSup.{u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (Lattice.toSemilatticeSup.{u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (ConditionallyCompleteLattice.toLattice.{u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (Subsemiring.completeLattice.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)))))) S T)) (HasSup.sup.{u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (SemilatticeSup.toHasSup.{u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (Lattice.toSemilatticeSup.{u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (ConditionallyCompleteLattice.toLattice.{u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (Subsemiring.completeLattice.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)))))) (SMul.smul.{u1, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (MulAction.toHasSmul.{u1, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) _inst_1 (Subsemiring.pointwiseMulAction.{u1, u2} M R _inst_1 _inst_2 _inst_3)) a S) (SMul.smul.{u1, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (MulAction.toHasSmul.{u1, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) _inst_1 (Subsemiring.pointwiseMulAction.{u1, u2} M R _inst_1 _inst_2 _inst_3)) a T))
but is expected to have type
  forall {M : Type.{u1}} {R : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Semiring.{u2} R] [_inst_3 : MulSemiringAction.{u1, u2} M R _inst_1 _inst_2] (a : M) (S : Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (T : Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)), Eq.{succ u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (HSMul.hSMul.{u1, u2, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (instHSMul.{u1, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (MulAction.toSMul.{u1, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) _inst_1 (Subsemiring.pointwiseMulAction.{u1, u2} M R _inst_1 _inst_2 _inst_3))) a (HasSup.sup.{u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (SemilatticeSup.toHasSup.{u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (Lattice.toSemilatticeSup.{u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (ConditionallyCompleteLattice.toLattice.{u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (Subsemiring.instCompleteLatticeSubsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)))))) S T)) (HasSup.sup.{u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (SemilatticeSup.toHasSup.{u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (Lattice.toSemilatticeSup.{u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (ConditionallyCompleteLattice.toLattice.{u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (Subsemiring.instCompleteLatticeSubsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)))))) (HSMul.hSMul.{u1, u2, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (instHSMul.{u1, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (MulAction.toSMul.{u1, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) _inst_1 (Subsemiring.pointwiseMulAction.{u1, u2} M R _inst_1 _inst_2 _inst_3))) a S) (HSMul.hSMul.{u1, u2, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (instHSMul.{u1, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (MulAction.toSMul.{u1, u2} M (Subsemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) _inst_1 (Subsemiring.pointwiseMulAction.{u1, u2} M R _inst_1 _inst_2 _inst_3))) a T))
Case conversion may be inaccurate. Consider using '#align subsemiring.smul_sup Subsemiring.smul_supₓ'. -/
theorem smul_sup (a : M) (S T : Subsemiring R) : a • (S ⊔ T) = a • S ⊔ a • T :=
  map_sup _ _ _
#align subsemiring.smul_sup Subsemiring.smul_sup

#print Subsemiring.smul_closure /-
theorem smul_closure (a : M) (s : Set R) : a • closure s = closure (a • s) :=
  RingHom.map_closureS _ _
#align subsemiring.smul_closure Subsemiring.smul_closure
-/

#print Subsemiring.pointwise_central_scalar /-
instance pointwise_central_scalar [MulSemiringAction Mᵐᵒᵖ R] [IsCentralScalar M R] :
    IsCentralScalar M (Subsemiring R) :=
  ⟨fun a S => (congr_arg fun f => S.map f) <| RingHom.ext <| op_smul_eq_smul _⟩
#align subsemiring.pointwise_central_scalar Subsemiring.pointwise_central_scalar
-/

end Monoid

section Group

variable [Group M] [Semiring R] [MulSemiringAction M R]

open Pointwise

#print Subsemiring.smul_mem_pointwise_smul_iff /-
@[simp]
theorem smul_mem_pointwise_smul_iff {a : M} {S : Subsemiring R} {x : R} : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff
#align subsemiring.smul_mem_pointwise_smul_iff Subsemiring.smul_mem_pointwise_smul_iff
-/

#print Subsemiring.mem_pointwise_smul_iff_inv_smul_mem /-
theorem mem_pointwise_smul_iff_inv_smul_mem {a : M} {S : Subsemiring R} {x : R} :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem
#align subsemiring.mem_pointwise_smul_iff_inv_smul_mem Subsemiring.mem_pointwise_smul_iff_inv_smul_mem
-/

#print Subsemiring.mem_inv_pointwise_smul_iff /-
theorem mem_inv_pointwise_smul_iff {a : M} {S : Subsemiring R} {x : R} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff
#align subsemiring.mem_inv_pointwise_smul_iff Subsemiring.mem_inv_pointwise_smul_iff
-/

#print Subsemiring.pointwise_smul_le_pointwise_smul_iff /-
@[simp]
theorem pointwise_smul_le_pointwise_smul_iff {a : M} {S T : Subsemiring R} :
    a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff
#align subsemiring.pointwise_smul_le_pointwise_smul_iff Subsemiring.pointwise_smul_le_pointwise_smul_iff
-/

#print Subsemiring.pointwise_smul_subset_iff /-
theorem pointwise_smul_subset_iff {a : M} {S T : Subsemiring R} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff
#align subsemiring.pointwise_smul_subset_iff Subsemiring.pointwise_smul_subset_iff
-/

#print Subsemiring.subset_pointwise_smul_iff /-
theorem subset_pointwise_smul_iff {a : M} {S T : Subsemiring R} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff
#align subsemiring.subset_pointwise_smul_iff Subsemiring.subset_pointwise_smul_iff
-/

/-! TODO: add `equiv_smul` like we have for subgroup. -/


end Group

section GroupWithZero

variable [GroupWithZero M] [Semiring R] [MulSemiringAction M R]

open Pointwise

#print Subsemiring.smul_mem_pointwise_smul_iff₀ /-
@[simp]
theorem smul_mem_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) (S : Subsemiring R) (x : R) :
    a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff₀ ha (S : Set R) x
#align subsemiring.smul_mem_pointwise_smul_iff₀ Subsemiring.smul_mem_pointwise_smul_iff₀
-/

#print Subsemiring.mem_pointwise_smul_iff_inv_smul_mem₀ /-
theorem mem_pointwise_smul_iff_inv_smul_mem₀ {a : M} (ha : a ≠ 0) (S : Subsemiring R) (x : R) :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set R) x
#align subsemiring.mem_pointwise_smul_iff_inv_smul_mem₀ Subsemiring.mem_pointwise_smul_iff_inv_smul_mem₀
-/

#print Subsemiring.mem_inv_pointwise_smul_iff₀ /-
theorem mem_inv_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) (S : Subsemiring R) (x : R) :
    x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff₀ ha (S : Set R) x
#align subsemiring.mem_inv_pointwise_smul_iff₀ Subsemiring.mem_inv_pointwise_smul_iff₀
-/

#print Subsemiring.pointwise_smul_le_pointwise_smul_iff₀ /-
@[simp]
theorem pointwise_smul_le_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) {S T : Subsemiring R} :
    a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff₀ ha
#align subsemiring.pointwise_smul_le_pointwise_smul_iff₀ Subsemiring.pointwise_smul_le_pointwise_smul_iff₀
-/

#print Subsemiring.pointwise_smul_le_iff₀ /-
theorem pointwise_smul_le_iff₀ {a : M} (ha : a ≠ 0) {S T : Subsemiring R} :
    a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff₀ ha
#align subsemiring.pointwise_smul_le_iff₀ Subsemiring.pointwise_smul_le_iff₀
-/

#print Subsemiring.le_pointwise_smul_iff₀ /-
theorem le_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) {S T : Subsemiring R} :
    S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff₀ ha
#align subsemiring.le_pointwise_smul_iff₀ Subsemiring.le_pointwise_smul_iff₀
-/

end GroupWithZero

end Subsemiring

