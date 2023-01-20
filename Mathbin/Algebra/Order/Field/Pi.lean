/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module algebra.order.field.pi
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Field.Basic
import Mathbin.Data.Fintype.Lattice

/-!
# Lemmas about (finite domain) functions into fields.

We split this from `algebra.order.field.basic` to avoid importing the finiteness hierarchy there.
-/


variable {α ι : Type _} [LinearOrderedSemifield α]

/- warning: pi.exists_forall_pos_add_lt -> Pi.exists_forall_pos_add_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : LinearOrderedSemifield.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1)))))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1)))))))] [_inst_3 : Finite.{succ u2} ι] {x : ι -> α} {y : ι -> α}, (forall (i : ι), LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1))))))) (x i) (y i)) -> (Exists.{succ u1} α (fun (ε : α) => And (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1))))))))))) ε) (forall (i : ι), LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1))))))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1))))))))) (x i) ε) (y i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : LinearOrderedSemifield.{u2} α] [_inst_2 : ExistsAddOfLE.{u2} α (Distrib.toAdd.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (StrictOrderedSemiring.toSemiring.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} α _inst_1)))))))) (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedSemiring.toPartialOrder.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} α _inst_1))))))] [_inst_3 : Finite.{succ u1} ι] {x : ι -> α} {y : ι -> α}, (forall (i : ι), LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedSemiring.toPartialOrder.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} α _inst_1)))))) (x i) (y i)) -> (Exists.{succ u2} α (fun (ε : α) => And (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedSemiring.toPartialOrder.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} α _inst_1)))))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (CommMonoidWithZero.toZero.{u2} α (CommGroupWithZero.toCommMonoidWithZero.{u2} α (Semifield.toCommGroupWithZero.{u2} α (LinearOrderedSemifield.toSemifield.{u2} α _inst_1)))))) ε) (forall (i : ι), LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedSemiring.toPartialOrder.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} α _inst_1)))))) (HAdd.hAdd.{u2, u2, u2} α α α (instHAdd.{u2} α (Distrib.toAdd.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (StrictOrderedSemiring.toSemiring.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} α _inst_1))))))))) (x i) ε) (y i))))
Case conversion may be inaccurate. Consider using '#align pi.exists_forall_pos_add_lt Pi.exists_forall_pos_add_ltₓ'. -/
theorem Pi.exists_forall_pos_add_lt [ExistsAddOfLE α] [Finite ι] {x y : ι → α}
    (h : ∀ i, x i < y i) : ∃ ε, 0 < ε ∧ ∀ i, x i + ε < y i :=
  by
  cases nonempty_fintype ι
  cases isEmpty_or_nonempty ι
  · exact ⟨1, zero_lt_one, isEmptyElim⟩
  choose ε hε hxε using fun i => exists_pos_add_of_lt' (h i)
  obtain rfl : x + ε = y := funext hxε
  have hε : 0 < finset.univ.inf' Finset.univ_nonempty ε := (Finset.lt_inf'_iff _).2 fun i _ => hε _
  exact
    ⟨_, half_pos hε, fun i =>
      add_lt_add_left ((half_lt_self hε).trans_le <| Finset.inf'_le _ <| Finset.mem_univ _) _⟩
#align pi.exists_forall_pos_add_lt Pi.exists_forall_pos_add_lt

