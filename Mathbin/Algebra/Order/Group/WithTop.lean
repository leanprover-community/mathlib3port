/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.group.with_top
! leanprover-community/mathlib commit a59dad53320b73ef180174aae867addd707ef00e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Group.Instances
import Mathbin.Algebra.Order.Monoid.WithTop

/-!
# Adjoining a top element to a `linear_ordered_add_comm_group_with_top`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/946
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α : Type _}

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup α] {a b c d : α}

#print WithTop.linearOrderedAddCommGroupWithTop /-
instance WithTop.linearOrderedAddCommGroupWithTop : LinearOrderedAddCommGroupWithTop (WithTop α) :=
  { WithTop.linearOrderedAddCommMonoidWithTop, Option.nontrivial with
    neg := Option.map fun a : α => -a
    neg_top := @Option.map_none _ _ fun a : α => -a
    add_neg_cancel := by 
      rintro (a | a) ha
      · exact (ha rfl).elim
      · exact with_top.coe_add.symm.trans (WithTop.coe_eq_coe.2 (add_neg_self a)) }
#align with_top.linear_ordered_add_comm_group_with_top WithTop.linearOrderedAddCommGroupWithTop
-/

/- warning: with_top.coe_neg -> WithTop.coe_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedAddCommGroup.{u1} α] (a : α), Eq.{succ u1} (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (OrderedAddCommGroup.toAddCommGroup.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))))) a)) (Neg.neg.{u1} (WithTop.{u1} α) (SubNegMonoid.toHasNeg.{u1} (WithTop.{u1} α) (LinearOrderedAddCommGroupWithTop.toSubNegMonoid.{u1} (WithTop.{u1} α) (WithTop.linearOrderedAddCommGroupWithTop.{u1} α _inst_1))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedAddCommGroup.{u1} α] (a : α), Eq.{succ u1} (WithTop.{u1} α) (WithTop.some.{u1} α (Neg.neg.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α (OrderedAddCommGroup.toAddCommGroup.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))))))) a)) (Neg.neg.{u1} (WithTop.{u1} α) (LinearOrderedAddCommGroupWithTop.toNeg.{u1} (WithTop.{u1} α) (WithTop.linearOrderedAddCommGroupWithTop.{u1} α _inst_1)) (WithTop.some.{u1} α a))
Case conversion may be inaccurate. Consider using '#align with_top.coe_neg WithTop.coe_negₓ'. -/
@[simp, norm_cast]
theorem WithTop.coe_neg (a : α) : ((-a : α) : WithTop α) = -a :=
  rfl
#align with_top.coe_neg WithTop.coe_neg

end LinearOrderedAddCommGroup

