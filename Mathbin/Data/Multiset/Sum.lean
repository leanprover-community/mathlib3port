/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.multiset.sum
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Multiset.Nodup

/-!
# Disjoint sum of multisets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the disjoint sum of two multisets as `multiset (α ⊕ β)`. Beware not to confuse
with the `multiset.sum` operation which computes the additive sum.

## Main declarations

* `multiset.disj_sum`: `s.disj_sum t` is the disjoint sum of `s` and `t`.
-/


open Sum

namespace Multiset

variable {α β : Type _} (s : Multiset α) (t : Multiset β)

#print Multiset.disjSum /-
/-- Disjoint sum of multisets. -/
def disjSum : Multiset (Sum α β) :=
  s.map inl + t.map inr
#align multiset.disj_sum Multiset.disjSum
-/

/- warning: multiset.zero_disj_sum -> Multiset.zero_disjSum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (t : Multiset.{u2} β), Eq.{succ (max u1 u2)} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (Multiset.disjSum.{u1, u2} α β (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α)))) t) (Multiset.map.{u2, max u1 u2} β (Sum.{u1, u2} α β) (Sum.inr.{u1, u2} α β) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (t : Multiset.{u1} β), Eq.{max (succ u2) (succ u1)} (Multiset.{max u1 u2} (Sum.{u2, u1} α β)) (Multiset.disjSum.{u2, u1} α β (OfNat.ofNat.{u2} (Multiset.{u2} α) 0 (Zero.toOfNat0.{u2} (Multiset.{u2} α) (Multiset.instZeroMultiset.{u2} α))) t) (Multiset.map.{u1, max u1 u2} β (Sum.{u2, u1} α β) (Sum.inr.{u2, u1} α β) t)
Case conversion may be inaccurate. Consider using '#align multiset.zero_disj_sum Multiset.zero_disjSumₓ'. -/
@[simp]
theorem zero_disjSum : (0 : Multiset α).disjSum t = t.map inr :=
  zero_add _
#align multiset.zero_disj_sum Multiset.zero_disjSum

/- warning: multiset.disj_sum_zero -> Multiset.disjSum_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Multiset.{u1} α), Eq.{succ (max u1 u2)} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (Multiset.disjSum.{u1, u2} α β s (OfNat.ofNat.{u2} (Multiset.{u2} β) 0 (OfNat.mk.{u2} (Multiset.{u2} β) 0 (Zero.zero.{u2} (Multiset.{u2} β) (Multiset.hasZero.{u2} β))))) (Multiset.map.{u1, max u1 u2} α (Sum.{u1, u2} α β) (Sum.inl.{u1, u2} α β) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Multiset.{u2} α), Eq.{max (succ u2) (succ u1)} (Multiset.{max u1 u2} (Sum.{u2, u1} α β)) (Multiset.disjSum.{u2, u1} α β s (OfNat.ofNat.{u1} (Multiset.{u1} β) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} β) (Multiset.instZeroMultiset.{u1} β)))) (Multiset.map.{u2, max u1 u2} α (Sum.{u2, u1} α β) (Sum.inl.{u2, u1} α β) s)
Case conversion may be inaccurate. Consider using '#align multiset.disj_sum_zero Multiset.disjSum_zeroₓ'. -/
@[simp]
theorem disjSum_zero : s.disjSum (0 : Multiset β) = s.map inl :=
  add_zero _
#align multiset.disj_sum_zero Multiset.disjSum_zero

/- warning: multiset.card_disj_sum -> Multiset.card_disjSum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Multiset.{u1} α) (t : Multiset.{u2} β), Eq.{1} Nat (coeFn.{succ (max u1 u2), succ (max u1 u2)} (AddMonoidHom.{max u1 u2, 0} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) Nat (AddMonoid.toAddZeroClass.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (AddRightCancelMonoid.toAddMonoid.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (AddCancelMonoid.toAddRightCancelMonoid.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (AddCancelCommMonoid.toAddCancelMonoid.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (Multiset.orderedCancelAddCommMonoid.{max u1 u2} (Sum.{u1, u2} α β))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{max u1 u2, 0} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) Nat (AddMonoid.toAddZeroClass.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (AddRightCancelMonoid.toAddMonoid.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (AddCancelMonoid.toAddRightCancelMonoid.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (AddCancelCommMonoid.toAddCancelMonoid.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (Multiset.orderedCancelAddCommMonoid.{max u1 u2} (Sum.{u1, u2} α β))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) -> Nat) (AddMonoidHom.hasCoeToFun.{max u1 u2, 0} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) Nat (AddMonoid.toAddZeroClass.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (AddRightCancelMonoid.toAddMonoid.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (AddCancelMonoid.toAddRightCancelMonoid.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (AddCancelCommMonoid.toAddCancelMonoid.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (Multiset.orderedCancelAddCommMonoid.{max u1 u2} (Sum.{u1, u2} α β))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{max u1 u2} (Sum.{u1, u2} α β)) (Multiset.disjSum.{u1, u2} α β s t)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s) (coeFn.{succ u2, succ u2} (AddMonoidHom.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u2} β) -> Nat) (AddMonoidHom.hasCoeToFun.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u2} β) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Multiset.{u2} α) (t : Multiset.{u1} β), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{max u2 u1} (Sum.{u2, u1} α β)) => Nat) (Multiset.disjSum.{u2, u1} α β s t)) (FunLike.coe.{succ (max u2 u1), succ (max u2 u1), 1} (AddMonoidHom.{max u2 u1, 0} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) Nat (AddMonoid.toAddZeroClass.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (AddRightCancelMonoid.toAddMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (AddCancelMonoid.toAddRightCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (AddCancelCommMonoid.toAddCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{max u2 u1} (Sum.{u2, u1} α β))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (fun (_x : Multiset.{max u2 u1} (Sum.{u2, u1} α β)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{max u2 u1} (Sum.{u2, u1} α β)) => Nat) _x) (AddHomClass.toFunLike.{max u2 u1, max u2 u1, 0} (AddMonoidHom.{max u2 u1, 0} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) Nat (AddMonoid.toAddZeroClass.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (AddRightCancelMonoid.toAddMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (AddCancelMonoid.toAddRightCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (AddCancelCommMonoid.toAddCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{max u2 u1} (Sum.{u2, u1} α β))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) Nat (AddZeroClass.toAdd.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (AddMonoid.toAddZeroClass.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (AddRightCancelMonoid.toAddMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (AddCancelMonoid.toAddRightCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (AddCancelCommMonoid.toAddCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{max u2 u1} (Sum.{u2, u1} α β)))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{max u2 u1, max u2 u1, 0} (AddMonoidHom.{max u2 u1, 0} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) Nat (AddMonoid.toAddZeroClass.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (AddRightCancelMonoid.toAddMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (AddCancelMonoid.toAddRightCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (AddCancelCommMonoid.toAddCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{max u2 u1} (Sum.{u2, u1} α β))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) Nat (AddMonoid.toAddZeroClass.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (AddRightCancelMonoid.toAddMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (AddCancelMonoid.toAddRightCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (AddCancelCommMonoid.toAddCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{max u2 u1} (Sum.{u2, u1} α β))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{max u2 u1, 0} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) Nat (AddMonoid.toAddZeroClass.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (AddRightCancelMonoid.toAddMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (AddCancelMonoid.toAddRightCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (AddCancelCommMonoid.toAddCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sum.{u2, u1} α β)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{max u2 u1} (Sum.{u2, u1} α β))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{max u2 u1} (Sum.{u2, u1} α β)) (Multiset.disjSum.{u2, u1} α β s t)) (HAdd.hAdd.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) s) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} β) => Nat) t) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) s) (instHAdd.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) s) instAddNat) (FunLike.coe.{succ u2, succ u2, 1} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) (fun (_x : Multiset.{u2} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} α) => Nat) _x) (AddHomClass.toFunLike.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddZeroClass.toAdd.{u2} (Multiset.{u2} α) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u2, 0} (Multiset.{u2} α) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} α) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} α) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} α) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u2} α) s) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} β) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} β) (fun (_x : Multiset.{u1} β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} β) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} β) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} β) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} β) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} β) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} β) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} β) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} β) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} β) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} β) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} β) t))
Case conversion may be inaccurate. Consider using '#align multiset.card_disj_sum Multiset.card_disjSumₓ'. -/
@[simp]
theorem card_disjSum : (s.disjSum t).card = s.card + t.card := by
  rw [disj_sum, card_add, card_map, card_map]
#align multiset.card_disj_sum Multiset.card_disjSum

variable {s t} {s₁ s₂ : Multiset α} {t₁ t₂ : Multiset β} {a : α} {b : β} {x : Sum α β}

/- warning: multiset.mem_disj_sum -> Multiset.mem_disjSum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Multiset.{u1} α} {t : Multiset.{u2} β} {x : Sum.{u1, u2} α β}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (Multiset.hasMem.{max u1 u2} (Sum.{u1, u2} α β)) x (Multiset.disjSum.{u1, u2} α β s t)) (Or (Exists.{succ u1} α (fun (a : α) => And (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) (Eq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β) (Sum.inl.{u1, u2} α β a) x))) (Exists.{succ u2} β (fun (b : β) => And (Membership.Mem.{u2, u2} β (Multiset.{u2} β) (Multiset.hasMem.{u2} β) b t) (Eq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β) (Sum.inr.{u1, u2} α β b) x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Multiset.{u2} α} {t : Multiset.{u1} β} {x : Sum.{u2, u1} α β}, Iff (Membership.mem.{max u2 u1, max u2 u1} (Sum.{u2, u1} α β) (Multiset.{max u1 u2} (Sum.{u2, u1} α β)) (Multiset.instMembershipMultiset.{max u2 u1} (Sum.{u2, u1} α β)) x (Multiset.disjSum.{u2, u1} α β s t)) (Or (Exists.{succ u2} α (fun (a : α) => And (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a s) (Eq.{max (succ u2) (succ u1)} (Sum.{u2, u1} α β) (Sum.inl.{u2, u1} α β a) x))) (Exists.{succ u1} β (fun (b : β) => And (Membership.mem.{u1, u1} β (Multiset.{u1} β) (Multiset.instMembershipMultiset.{u1} β) b t) (Eq.{max (succ u2) (succ u1)} (Sum.{u2, u1} α β) (Sum.inr.{u2, u1} α β b) x))))
Case conversion may be inaccurate. Consider using '#align multiset.mem_disj_sum Multiset.mem_disjSumₓ'. -/
theorem mem_disjSum : x ∈ s.disjSum t ↔ (∃ a, a ∈ s ∧ inl a = x) ∨ ∃ b, b ∈ t ∧ inr b = x := by
  simp_rw [disj_sum, mem_add, mem_map]
#align multiset.mem_disj_sum Multiset.mem_disjSum

#print Multiset.inl_mem_disjSum /-
@[simp]
theorem inl_mem_disjSum : inl a ∈ s.disjSum t ↔ a ∈ s :=
  by
  rw [mem_disj_sum, or_iff_left]
  simp only [exists_eq_right]
  rintro ⟨b, _, hb⟩
  exact inr_ne_inl hb
#align multiset.inl_mem_disj_sum Multiset.inl_mem_disjSum
-/

#print Multiset.inr_mem_disjSum /-
@[simp]
theorem inr_mem_disjSum : inr b ∈ s.disjSum t ↔ b ∈ t :=
  by
  rw [mem_disj_sum, or_iff_right]
  simp only [exists_eq_right]
  rintro ⟨a, _, ha⟩
  exact inl_ne_inr ha
#align multiset.inr_mem_disj_sum Multiset.inr_mem_disjSum
-/

/- warning: multiset.disj_sum_mono -> Multiset.disjSum_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Multiset.{u1} α} {s₂ : Multiset.{u1} α} {t₁ : Multiset.{u2} β} {t₂ : Multiset.{u2} β}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s₁ s₂) -> (LE.le.{u2} (Multiset.{u2} β) (Preorder.toLE.{u2} (Multiset.{u2} β) (PartialOrder.toPreorder.{u2} (Multiset.{u2} β) (Multiset.partialOrder.{u2} β))) t₁ t₂) -> (LE.le.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (Preorder.toLE.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (PartialOrder.toPreorder.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (Multiset.partialOrder.{max u1 u2} (Sum.{u1, u2} α β)))) (Multiset.disjSum.{u1, u2} α β s₁ t₁) (Multiset.disjSum.{u1, u2} α β s₂ t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Multiset.{u2} α} {s₂ : Multiset.{u2} α} {t₁ : Multiset.{u1} β} {t₂ : Multiset.{u1} β}, (LE.le.{u2} (Multiset.{u2} α) (Preorder.toLE.{u2} (Multiset.{u2} α) (PartialOrder.toPreorder.{u2} (Multiset.{u2} α) (Multiset.instPartialOrderMultiset.{u2} α))) s₁ s₂) -> (LE.le.{u1} (Multiset.{u1} β) (Preorder.toLE.{u1} (Multiset.{u1} β) (PartialOrder.toPreorder.{u1} (Multiset.{u1} β) (Multiset.instPartialOrderMultiset.{u1} β))) t₁ t₂) -> (LE.le.{max u2 u1} (Multiset.{max u1 u2} (Sum.{u2, u1} α β)) (Preorder.toLE.{max u2 u1} (Multiset.{max u1 u2} (Sum.{u2, u1} α β)) (PartialOrder.toPreorder.{max u2 u1} (Multiset.{max u1 u2} (Sum.{u2, u1} α β)) (Multiset.instPartialOrderMultiset.{max u2 u1} (Sum.{u2, u1} α β)))) (Multiset.disjSum.{u2, u1} α β s₁ t₁) (Multiset.disjSum.{u2, u1} α β s₂ t₂))
Case conversion may be inaccurate. Consider using '#align multiset.disj_sum_mono Multiset.disjSum_monoₓ'. -/
theorem disjSum_mono (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) : s₁.disjSum t₁ ≤ s₂.disjSum t₂ :=
  add_le_add (map_le_map hs) (map_le_map ht)
#align multiset.disj_sum_mono Multiset.disjSum_mono

/- warning: multiset.disj_sum_mono_left -> Multiset.disjSum_mono_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (t : Multiset.{u2} β), Monotone.{u1, max u1 u2} (Multiset.{u1} α) (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α)) (PartialOrder.toPreorder.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (Multiset.partialOrder.{max u1 u2} (Sum.{u1, u2} α β))) (fun (s : Multiset.{u1} α) => Multiset.disjSum.{u1, u2} α β s t)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (t : Multiset.{u2} β), Monotone.{u1, max u1 u2} (Multiset.{u1} α) (Multiset.{max u2 u1} (Sum.{u1, u2} α β)) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α)) (PartialOrder.toPreorder.{max u1 u2} (Multiset.{max u2 u1} (Sum.{u1, u2} α β)) (Multiset.instPartialOrderMultiset.{max u1 u2} (Sum.{u1, u2} α β))) (fun (s : Multiset.{u1} α) => Multiset.disjSum.{u1, u2} α β s t)
Case conversion may be inaccurate. Consider using '#align multiset.disj_sum_mono_left Multiset.disjSum_mono_leftₓ'. -/
theorem disjSum_mono_left (t : Multiset β) : Monotone fun s : Multiset α => s.disjSum t :=
  fun s₁ s₂ hs => add_le_add_right (map_le_map hs) _
#align multiset.disj_sum_mono_left Multiset.disjSum_mono_left

/- warning: multiset.disj_sum_mono_right -> Multiset.disjSum_mono_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Multiset.{u1} α), Monotone.{u2, max u1 u2} (Multiset.{u2} β) (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (PartialOrder.toPreorder.{u2} (Multiset.{u2} β) (Multiset.partialOrder.{u2} β)) (PartialOrder.toPreorder.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (Multiset.partialOrder.{max u1 u2} (Sum.{u1, u2} α β))) (Multiset.disjSum.{u1, u2} α β s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Multiset.{u2} α), Monotone.{u1, max u2 u1} (Multiset.{u1} β) (Multiset.{max u1 u2} (Sum.{u2, u1} α β)) (PartialOrder.toPreorder.{u1} (Multiset.{u1} β) (Multiset.instPartialOrderMultiset.{u1} β)) (PartialOrder.toPreorder.{max u2 u1} (Multiset.{max u1 u2} (Sum.{u2, u1} α β)) (Multiset.instPartialOrderMultiset.{max u2 u1} (Sum.{u2, u1} α β))) (Multiset.disjSum.{u2, u1} α β s)
Case conversion may be inaccurate. Consider using '#align multiset.disj_sum_mono_right Multiset.disjSum_mono_rightₓ'. -/
theorem disjSum_mono_right (s : Multiset α) :
    Monotone (s.disjSum : Multiset β → Multiset (Sum α β)) := fun t₁ t₂ ht =>
  add_le_add_left (map_le_map ht) _
#align multiset.disj_sum_mono_right Multiset.disjSum_mono_right

/- warning: multiset.disj_sum_lt_disj_sum_of_lt_of_le -> Multiset.disjSum_lt_disjSum_of_lt_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Multiset.{u1} α} {s₂ : Multiset.{u1} α} {t₁ : Multiset.{u2} β} {t₂ : Multiset.{u2} β}, (LT.lt.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s₁ s₂) -> (LE.le.{u2} (Multiset.{u2} β) (Preorder.toLE.{u2} (Multiset.{u2} β) (PartialOrder.toPreorder.{u2} (Multiset.{u2} β) (Multiset.partialOrder.{u2} β))) t₁ t₂) -> (LT.lt.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (Preorder.toLT.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (PartialOrder.toPreorder.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (Multiset.partialOrder.{max u1 u2} (Sum.{u1, u2} α β)))) (Multiset.disjSum.{u1, u2} α β s₁ t₁) (Multiset.disjSum.{u1, u2} α β s₂ t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Multiset.{u2} α} {s₂ : Multiset.{u2} α} {t₁ : Multiset.{u1} β} {t₂ : Multiset.{u1} β}, (LT.lt.{u2} (Multiset.{u2} α) (Preorder.toLT.{u2} (Multiset.{u2} α) (PartialOrder.toPreorder.{u2} (Multiset.{u2} α) (Multiset.instPartialOrderMultiset.{u2} α))) s₁ s₂) -> (LE.le.{u1} (Multiset.{u1} β) (Preorder.toLE.{u1} (Multiset.{u1} β) (PartialOrder.toPreorder.{u1} (Multiset.{u1} β) (Multiset.instPartialOrderMultiset.{u1} β))) t₁ t₂) -> (LT.lt.{max u2 u1} (Multiset.{max u1 u2} (Sum.{u2, u1} α β)) (Preorder.toLT.{max u2 u1} (Multiset.{max u1 u2} (Sum.{u2, u1} α β)) (PartialOrder.toPreorder.{max u2 u1} (Multiset.{max u1 u2} (Sum.{u2, u1} α β)) (Multiset.instPartialOrderMultiset.{max u2 u1} (Sum.{u2, u1} α β)))) (Multiset.disjSum.{u2, u1} α β s₁ t₁) (Multiset.disjSum.{u2, u1} α β s₂ t₂))
Case conversion may be inaccurate. Consider using '#align multiset.disj_sum_lt_disj_sum_of_lt_of_le Multiset.disjSum_lt_disjSum_of_lt_of_leₓ'. -/
theorem disjSum_lt_disjSum_of_lt_of_le (hs : s₁ < s₂) (ht : t₁ ≤ t₂) :
    s₁.disjSum t₁ < s₂.disjSum t₂ :=
  add_lt_add_of_lt_of_le (map_lt_map hs) (map_le_map ht)
#align multiset.disj_sum_lt_disj_sum_of_lt_of_le Multiset.disjSum_lt_disjSum_of_lt_of_le

/- warning: multiset.disj_sum_lt_disj_sum_of_le_of_lt -> Multiset.disjSum_lt_disjSum_of_le_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Multiset.{u1} α} {s₂ : Multiset.{u1} α} {t₁ : Multiset.{u2} β} {t₂ : Multiset.{u2} β}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s₁ s₂) -> (LT.lt.{u2} (Multiset.{u2} β) (Preorder.toLT.{u2} (Multiset.{u2} β) (PartialOrder.toPreorder.{u2} (Multiset.{u2} β) (Multiset.partialOrder.{u2} β))) t₁ t₂) -> (LT.lt.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (Preorder.toLT.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (PartialOrder.toPreorder.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (Multiset.partialOrder.{max u1 u2} (Sum.{u1, u2} α β)))) (Multiset.disjSum.{u1, u2} α β s₁ t₁) (Multiset.disjSum.{u1, u2} α β s₂ t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Multiset.{u2} α} {s₂ : Multiset.{u2} α} {t₁ : Multiset.{u1} β} {t₂ : Multiset.{u1} β}, (LE.le.{u2} (Multiset.{u2} α) (Preorder.toLE.{u2} (Multiset.{u2} α) (PartialOrder.toPreorder.{u2} (Multiset.{u2} α) (Multiset.instPartialOrderMultiset.{u2} α))) s₁ s₂) -> (LT.lt.{u1} (Multiset.{u1} β) (Preorder.toLT.{u1} (Multiset.{u1} β) (PartialOrder.toPreorder.{u1} (Multiset.{u1} β) (Multiset.instPartialOrderMultiset.{u1} β))) t₁ t₂) -> (LT.lt.{max u2 u1} (Multiset.{max u1 u2} (Sum.{u2, u1} α β)) (Preorder.toLT.{max u2 u1} (Multiset.{max u1 u2} (Sum.{u2, u1} α β)) (PartialOrder.toPreorder.{max u2 u1} (Multiset.{max u1 u2} (Sum.{u2, u1} α β)) (Multiset.instPartialOrderMultiset.{max u2 u1} (Sum.{u2, u1} α β)))) (Multiset.disjSum.{u2, u1} α β s₁ t₁) (Multiset.disjSum.{u2, u1} α β s₂ t₂))
Case conversion may be inaccurate. Consider using '#align multiset.disj_sum_lt_disj_sum_of_le_of_lt Multiset.disjSum_lt_disjSum_of_le_of_ltₓ'. -/
theorem disjSum_lt_disjSum_of_le_of_lt (hs : s₁ ≤ s₂) (ht : t₁ < t₂) :
    s₁.disjSum t₁ < s₂.disjSum t₂ :=
  add_lt_add_of_le_of_lt (map_le_map hs) (map_lt_map ht)
#align multiset.disj_sum_lt_disj_sum_of_le_of_lt Multiset.disjSum_lt_disjSum_of_le_of_lt

/- warning: multiset.disj_sum_strict_mono_left -> Multiset.disjSum_strictMono_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (t : Multiset.{u2} β), StrictMono.{u1, max u1 u2} (Multiset.{u1} α) (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α)) (PartialOrder.toPreorder.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (Multiset.partialOrder.{max u1 u2} (Sum.{u1, u2} α β))) (fun (s : Multiset.{u1} α) => Multiset.disjSum.{u1, u2} α β s t)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (t : Multiset.{u2} β), StrictMono.{u1, max u1 u2} (Multiset.{u1} α) (Multiset.{max u2 u1} (Sum.{u1, u2} α β)) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α)) (PartialOrder.toPreorder.{max u1 u2} (Multiset.{max u2 u1} (Sum.{u1, u2} α β)) (Multiset.instPartialOrderMultiset.{max u1 u2} (Sum.{u1, u2} α β))) (fun (s : Multiset.{u1} α) => Multiset.disjSum.{u1, u2} α β s t)
Case conversion may be inaccurate. Consider using '#align multiset.disj_sum_strict_mono_left Multiset.disjSum_strictMono_leftₓ'. -/
theorem disjSum_strictMono_left (t : Multiset β) : StrictMono fun s : Multiset α => s.disjSum t :=
  fun s₁ s₂ hs => disjSum_lt_disjSum_of_lt_of_le hs le_rfl
#align multiset.disj_sum_strict_mono_left Multiset.disjSum_strictMono_left

/- warning: multiset.disj_sum_strict_mono_right -> Multiset.disjSum_strictMono_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Multiset.{u1} α), StrictMono.{u2, max u1 u2} (Multiset.{u2} β) (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (PartialOrder.toPreorder.{u2} (Multiset.{u2} β) (Multiset.partialOrder.{u2} β)) (PartialOrder.toPreorder.{max u1 u2} (Multiset.{max u1 u2} (Sum.{u1, u2} α β)) (Multiset.partialOrder.{max u1 u2} (Sum.{u1, u2} α β))) (Multiset.disjSum.{u1, u2} α β s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Multiset.{u2} α), StrictMono.{u1, max u2 u1} (Multiset.{u1} β) (Multiset.{max u1 u2} (Sum.{u2, u1} α β)) (PartialOrder.toPreorder.{u1} (Multiset.{u1} β) (Multiset.instPartialOrderMultiset.{u1} β)) (PartialOrder.toPreorder.{max u2 u1} (Multiset.{max u1 u2} (Sum.{u2, u1} α β)) (Multiset.instPartialOrderMultiset.{max u2 u1} (Sum.{u2, u1} α β))) (Multiset.disjSum.{u2, u1} α β s)
Case conversion may be inaccurate. Consider using '#align multiset.disj_sum_strict_mono_right Multiset.disjSum_strictMono_rightₓ'. -/
theorem disjSum_strictMono_right (s : Multiset α) :
    StrictMono (s.disjSum : Multiset β → Multiset (Sum α β)) := fun s₁ s₂ =>
  disjSum_lt_disjSum_of_le_of_lt le_rfl
#align multiset.disj_sum_strict_mono_right Multiset.disjSum_strictMono_right

/- warning: multiset.nodup.disj_sum -> Multiset.Nodup.disjSum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Multiset.{u1} α} {t : Multiset.{u2} β}, (Multiset.Nodup.{u1} α s) -> (Multiset.Nodup.{u2} β t) -> (Multiset.Nodup.{max u1 u2} (Sum.{u1, u2} α β) (Multiset.disjSum.{u1, u2} α β s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Multiset.{u2} α} {t : Multiset.{u1} β}, (Multiset.Nodup.{u2} α s) -> (Multiset.Nodup.{u1} β t) -> (Multiset.Nodup.{max u2 u1} (Sum.{u2, u1} α β) (Multiset.disjSum.{u2, u1} α β s t))
Case conversion may be inaccurate. Consider using '#align multiset.nodup.disj_sum Multiset.Nodup.disjSumₓ'. -/
protected theorem Nodup.disjSum (hs : s.Nodup) (ht : t.Nodup) : (s.disjSum t).Nodup :=
  by
  refine' ((hs.map inl_injective).add_iff <| ht.map inr_injective).2 fun x hs ht => _
  rw [Multiset.mem_map] at hs ht
  obtain ⟨a, _, rfl⟩ := hs
  obtain ⟨b, _, h⟩ := ht
  exact inr_ne_inl h
#align multiset.nodup.disj_sum Multiset.Nodup.disjSum

end Multiset

