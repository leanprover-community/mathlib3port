/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.multiset.bind
! leanprover-community/mathlib commit 008205aa645b3f194c1da47025c5f110c8406eab
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Multiset.Basic

/-!
# Bind operation for multisets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a few basic operations on `multiset`, notably the monadic bind.

## Main declarations

* `multiset.join`: The join, aka union or sum, of multisets.
* `multiset.bind`: The bind of a multiset-indexed family of multisets.
* `multiset.product`: Cartesian product of two multisets.
* `multiset.sigma`: Disjoint sum of multisets in a sigma type.
-/


variable {α β γ δ : Type _}

namespace Multiset

/-! ### Join -/


#print Multiset.join /-
/-- `join S`, where `S` is a multiset of multisets, is the lift of the list join
  operation, that is, the union of all the sets.
     join {{1, 2}, {1, 2}, {0, 1}} = {0, 1, 1, 1, 2, 2} -/
def join : Multiset (Multiset α) → Multiset α :=
  Sum
#align multiset.join Multiset.join
-/

#print Multiset.coe_join /-
theorem coe_join :
    ∀ L : List (List α), join (L.map (@coe _ (Multiset α) _) : Multiset (Multiset α)) = L.join
  | [] => rfl
  | l :: L => congr_arg (fun s : Multiset α => ↑l + s) (coe_join L)
#align multiset.coe_join Multiset.coe_join
-/

#print Multiset.join_zero /-
@[simp]
theorem join_zero : @join α 0 = 0 :=
  rfl
#align multiset.join_zero Multiset.join_zero
-/

#print Multiset.join_cons /-
@[simp]
theorem join_cons (s S) : @join α (s ::ₘ S) = s + join S :=
  sum_cons _ _
#align multiset.join_cons Multiset.join_cons
-/

#print Multiset.join_add /-
@[simp]
theorem join_add (S T) : @join α (S + T) = join S + join T :=
  sum_add _ _
#align multiset.join_add Multiset.join_add
-/

#print Multiset.singleton_join /-
@[simp]
theorem singleton_join (a) : join ({a} : Multiset (Multiset α)) = a :=
  sum_singleton _
#align multiset.singleton_join Multiset.singleton_join
-/

/- warning: multiset.mem_join -> Multiset.mem_join is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {S : Multiset.{u1} (Multiset.{u1} α)}, Iff (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a (Multiset.join.{u1} α S)) (Exists.{succ u1} (Multiset.{u1} α) (fun (s : Multiset.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} (Multiset.{u1} α)) (Multiset.hasMem.{u1} (Multiset.{u1} α)) s S) (fun (H : Membership.Mem.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} (Multiset.{u1} α)) (Multiset.hasMem.{u1} (Multiset.{u1} α)) s S) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s)))
but is expected to have type
  forall {α : Type.{u1}} {a : α} {S : Multiset.{u1} (Multiset.{u1} α)}, Iff (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a (Multiset.join.{u1} α S)) (Exists.{succ u1} (Multiset.{u1} α) (fun (s : Multiset.{u1} α) => And (Membership.mem.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} (Multiset.{u1} α)) (Multiset.instMembershipMultiset.{u1} (Multiset.{u1} α)) s S) (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a s)))
Case conversion may be inaccurate. Consider using '#align multiset.mem_join Multiset.mem_joinₓ'. -/
@[simp]
theorem mem_join {a S} : a ∈ @join α S ↔ ∃ s ∈ S, a ∈ s :=
  Multiset.induction_on S (by simp) <| by
    simp (config := { contextual := true }) [or_and_right, exists_or]
#align multiset.mem_join Multiset.mem_join

/- warning: multiset.card_join -> Multiset.card_join is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (S : Multiset.{u1} (Multiset.{u1} α)), Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (Multiset.join.{u1} α S)) (Multiset.sum.{0} Nat Nat.addCommMonoid (Multiset.map.{u1, 0} (Multiset.{u1} α) Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α)) S))
but is expected to have type
  forall {α : Type.{u1}} (S : Multiset.{u1} (Multiset.{u1} α)), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.join.{u1} α S)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (Multiset.join.{u1} α S)) (Multiset.sum.{0} Nat Nat.addCommMonoid (Multiset.map.{u1, 0} (Multiset.{u1} α) Nat (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α)) S))
Case conversion may be inaccurate. Consider using '#align multiset.card_join Multiset.card_joinₓ'. -/
@[simp]
theorem card_join (S) : card (@join α S) = sum (map card S) :=
  Multiset.induction_on S (by simp) (by simp)
#align multiset.card_join Multiset.card_join

/- warning: multiset.rel_join -> Multiset.rel_join is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} {s : Multiset.{u1} (Multiset.{u1} α)} {t : Multiset.{u2} (Multiset.{u2} β)}, (Multiset.Rel.{u1, u2} (Multiset.{u1} α) (Multiset.{u2} β) (Multiset.Rel.{u1, u2} α β r) s t) -> (Multiset.Rel.{u1, u2} α β r (Multiset.join.{u1} α s) (Multiset.join.{u2} β t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop} {s : Multiset.{u2} (Multiset.{u2} α)} {t : Multiset.{u1} (Multiset.{u1} β)}, (Multiset.Rel.{u2, u1} (Multiset.{u2} α) (Multiset.{u1} β) (Multiset.Rel.{u2, u1} α β r) s t) -> (Multiset.Rel.{u2, u1} α β r (Multiset.join.{u2} α s) (Multiset.join.{u1} β t))
Case conversion may be inaccurate. Consider using '#align multiset.rel_join Multiset.rel_joinₓ'. -/
theorem rel_join {r : α → β → Prop} {s t} (h : Rel (Rel r) s t) : Rel r s.join t.join :=
  by
  induction h
  case zero => simp
  case cons a b s t hab hst ih => simpa using hab.add ih
#align multiset.rel_join Multiset.rel_join

/-! ### Bind -/


section Bind

variable (a : α) (s t : Multiset α) (f g : α → Multiset β)

#print Multiset.bind /-
/-- `s.bind f` is the monad bind operation, defined as `(s.map f).join`. It is the union of `f a` as
`a` ranges over `s`. -/
def bind (s : Multiset α) (f : α → Multiset β) : Multiset β :=
  (s.map f).join
#align multiset.bind Multiset.bind
-/

/- warning: multiset.coe_bind -> Multiset.coe_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l : List.{u1} α) (f : α -> (List.{u2} β)), Eq.{succ u2} (Multiset.{u2} β) (Multiset.bind.{u1, u2} α β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) l) (fun (a : α) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (List.{u2} β) (Multiset.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (List.{u2} β) (Multiset.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (List.{u2} β) (Multiset.{u2} β) (coeBase.{succ u2, succ u2} (List.{u2} β) (Multiset.{u2} β) (Multiset.hasCoe.{u2} β)))) (f a))) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (List.{u2} β) (Multiset.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (List.{u2} β) (Multiset.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (List.{u2} β) (Multiset.{u2} β) (coeBase.{succ u2, succ u2} (List.{u2} β) (Multiset.{u2} β) (Multiset.hasCoe.{u2} β)))) (List.bind.{u1, u2} α β l f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (l : List.{u2} α) (f : α -> (List.{u1} β)), Eq.{succ u1} (Multiset.{u1} β) (Multiset.bind.{u2, u1} α β (Multiset.ofList.{u2} α l) (fun (a : α) => Multiset.ofList.{u1} β (f a))) (Multiset.ofList.{u1} β (List.bind.{u2, u1} α β l f))
Case conversion may be inaccurate. Consider using '#align multiset.coe_bind Multiset.coe_bindₓ'. -/
@[simp]
theorem coe_bind (l : List α) (f : α → List β) : (@bind α β l fun a => f a) = l.bind f := by
  rw [List.bind, ← coe_join, List.map_map] <;> rfl
#align multiset.coe_bind Multiset.coe_bind

#print Multiset.zero_bind /-
@[simp]
theorem zero_bind : bind 0 f = 0 :=
  rfl
#align multiset.zero_bind Multiset.zero_bind
-/

#print Multiset.cons_bind /-
@[simp]
theorem cons_bind : (a ::ₘ s).bind f = f a + s.bind f := by simp [bind]
#align multiset.cons_bind Multiset.cons_bind
-/

#print Multiset.singleton_bind /-
@[simp]
theorem singleton_bind : bind {a} f = f a := by simp [bind]
#align multiset.singleton_bind Multiset.singleton_bind
-/

#print Multiset.add_bind /-
@[simp]
theorem add_bind : (s + t).bind f = s.bind f + t.bind f := by simp [bind]
#align multiset.add_bind Multiset.add_bind
-/

#print Multiset.bind_zero /-
@[simp]
theorem bind_zero : s.bind (fun a => 0 : α → Multiset β) = 0 := by simp [bind, join, nsmul_zero]
#align multiset.bind_zero Multiset.bind_zero
-/

#print Multiset.bind_add /-
@[simp]
theorem bind_add : (s.bind fun a => f a + g a) = s.bind f + s.bind g := by simp [bind, join]
#align multiset.bind_add Multiset.bind_add
-/

#print Multiset.bind_cons /-
@[simp]
theorem bind_cons (f : α → β) (g : α → Multiset β) :
    (s.bind fun a => f a ::ₘ g a) = map f s + s.bind g :=
  Multiset.induction_on s (by simp)
    (by simp (config := { contextual := true }) [add_comm, add_left_comm])
#align multiset.bind_cons Multiset.bind_cons
-/

#print Multiset.bind_singleton /-
@[simp]
theorem bind_singleton (f : α → β) : (s.bind fun x => ({f x} : Multiset β)) = map f s :=
  Multiset.induction_on s (by rw [zero_bind, map_zero]) (by simp [singleton_add])
#align multiset.bind_singleton Multiset.bind_singleton
-/

/- warning: multiset.mem_bind -> Multiset.mem_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {b : β} {s : Multiset.{u1} α} {f : α -> (Multiset.{u2} β)}, Iff (Membership.Mem.{u2, u2} β (Multiset.{u2} β) (Multiset.hasMem.{u2} β) b (Multiset.bind.{u1, u2} α β s f)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Multiset.{u2} β) (Multiset.hasMem.{u2} β) b (f a))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {b : β} {s : Multiset.{u2} α} {f : α -> (Multiset.{u1} β)}, Iff (Membership.mem.{u1, u1} β (Multiset.{u1} β) (Multiset.instMembershipMultiset.{u1} β) b (Multiset.bind.{u2, u1} α β s f)) (Exists.{succ u2} α (fun (a : α) => And (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a s) (Membership.mem.{u1, u1} β (Multiset.{u1} β) (Multiset.instMembershipMultiset.{u1} β) b (f a))))
Case conversion may be inaccurate. Consider using '#align multiset.mem_bind Multiset.mem_bindₓ'. -/
@[simp]
theorem mem_bind {b s} {f : α → Multiset β} : b ∈ bind s f ↔ ∃ a ∈ s, b ∈ f a := by
  simp [bind] <;> simp [-exists_and_right, exists_and_distrib_right.symm] <;> rw [exists_swap] <;>
    simp [and_assoc']
#align multiset.mem_bind Multiset.mem_bind

/- warning: multiset.card_bind -> Multiset.card_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Multiset.{u1} α) (f : α -> (Multiset.{u2} β)), Eq.{1} Nat (coeFn.{succ u2, succ u2} (AddMonoidHom.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toCancelAddMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toCancelAddMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u2} β) -> Nat) (AddMonoidHom.hasCoeToFun.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toCancelAddMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u2} β) (Multiset.bind.{u1, u2} α β s f)) (Multiset.sum.{0} Nat Nat.addCommMonoid (Multiset.map.{u1, 0} α Nat (Function.comp.{succ u1, succ u2, 1} α (Multiset.{u2} β) Nat (coeFn.{succ u2, succ u2} (AddMonoidHom.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toCancelAddMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toCancelAddMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u2} β) -> Nat) (AddMonoidHom.hasCoeToFun.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toCancelAddMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u2} β)) f) s))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Multiset.{u1} α) (f : α -> (Multiset.{u2} β)), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} β) => Nat) (Multiset.bind.{u1, u2} α β s f)) (FunLike.coe.{succ u2, succ u2, 1} (AddMonoidHom.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} β) (fun (_x : Multiset.{u2} β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} β) => Nat) _x) (AddHomClass.toFunLike.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} β) Nat (AddZeroClass.toAdd.{u2} (Multiset.{u2} β) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} β))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u2} β) (Multiset.bind.{u1, u2} α β s f)) (Multiset.sum.{0} Nat Nat.addCommMonoid (Multiset.map.{u1, 0} α Nat (Function.comp.{succ u1, succ u2, 1} α (Multiset.{u2} β) Nat (FunLike.coe.{succ u2, succ u2, 1} (AddMonoidHom.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} β) (fun (_x : Multiset.{u2} β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} β) => Nat) _x) (AddHomClass.toFunLike.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} β) Nat (AddZeroClass.toAdd.{u2} (Multiset.{u2} β) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} β))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u2} β)) f) s))
Case conversion may be inaccurate. Consider using '#align multiset.card_bind Multiset.card_bindₓ'. -/
@[simp]
theorem card_bind : (s.bind f).card = (s.map (card ∘ f)).Sum := by simp [bind]
#align multiset.card_bind Multiset.card_bind

#print Multiset.bind_congr /-
theorem bind_congr {f g : α → Multiset β} {m : Multiset α} :
    (∀ a ∈ m, f a = g a) → bind m f = bind m g := by simp (config := { contextual := true }) [bind]
#align multiset.bind_congr Multiset.bind_congr
-/

#print Multiset.bind_hcongr /-
theorem bind_hcongr {β' : Type _} {m : Multiset α} {f : α → Multiset β} {f' : α → Multiset β'}
    (h : β = β') (hf : ∀ a ∈ m, HEq (f a) (f' a)) : HEq (bind m f) (bind m f') := by subst h;
  simp at hf; simp [bind_congr hf]
#align multiset.bind_hcongr Multiset.bind_hcongr
-/

/- warning: multiset.map_bind -> Multiset.map_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (m : Multiset.{u1} α) (n : α -> (Multiset.{u2} β)) (f : β -> γ), Eq.{succ u3} (Multiset.{u3} γ) (Multiset.map.{u2, u3} β γ f (Multiset.bind.{u1, u2} α β m n)) (Multiset.bind.{u1, u3} α γ m (fun (a : α) => Multiset.map.{u2, u3} β γ f (n a)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (m : Multiset.{u3} α) (n : α -> (Multiset.{u2} β)) (f : β -> γ), Eq.{succ u1} (Multiset.{u1} γ) (Multiset.map.{u2, u1} β γ f (Multiset.bind.{u3, u2} α β m n)) (Multiset.bind.{u3, u1} α γ m (fun (a : α) => Multiset.map.{u2, u1} β γ f (n a)))
Case conversion may be inaccurate. Consider using '#align multiset.map_bind Multiset.map_bindₓ'. -/
theorem map_bind (m : Multiset α) (n : α → Multiset β) (f : β → γ) :
    map f (bind m n) = bind m fun a => map f (n a) :=
  Multiset.induction_on m (by simp) (by simp (config := { contextual := true }))
#align multiset.map_bind Multiset.map_bind

/- warning: multiset.bind_map -> Multiset.bind_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (m : Multiset.{u1} α) (n : β -> (Multiset.{u3} γ)) (f : α -> β), Eq.{succ u3} (Multiset.{u3} γ) (Multiset.bind.{u2, u3} β γ (Multiset.map.{u1, u2} α β f m) n) (Multiset.bind.{u1, u3} α γ m (fun (a : α) => n (f a)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} (m : Multiset.{u3} α) (n : β -> (Multiset.{u2} γ)) (f : α -> β), Eq.{succ u2} (Multiset.{u2} γ) (Multiset.bind.{u1, u2} β γ (Multiset.map.{u3, u1} α β f m) n) (Multiset.bind.{u3, u2} α γ m (fun (a : α) => n (f a)))
Case conversion may be inaccurate. Consider using '#align multiset.bind_map Multiset.bind_mapₓ'. -/
theorem bind_map (m : Multiset α) (n : β → Multiset γ) (f : α → β) :
    bind (map f m) n = bind m fun a => n (f a) :=
  Multiset.induction_on m (by simp) (by simp (config := { contextual := true }))
#align multiset.bind_map Multiset.bind_map

/- warning: multiset.bind_assoc -> Multiset.bind_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {s : Multiset.{u1} α} {f : α -> (Multiset.{u2} β)} {g : β -> (Multiset.{u3} γ)}, Eq.{succ u3} (Multiset.{u3} γ) (Multiset.bind.{u2, u3} β γ (Multiset.bind.{u1, u2} α β s f) g) (Multiset.bind.{u1, u3} α γ s (fun (a : α) => Multiset.bind.{u2, u3} β γ (f a) g))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {s : Multiset.{u3} α} {f : α -> (Multiset.{u2} β)} {g : β -> (Multiset.{u1} γ)}, Eq.{succ u1} (Multiset.{u1} γ) (Multiset.bind.{u2, u1} β γ (Multiset.bind.{u3, u2} α β s f) g) (Multiset.bind.{u3, u1} α γ s (fun (a : α) => Multiset.bind.{u2, u1} β γ (f a) g))
Case conversion may be inaccurate. Consider using '#align multiset.bind_assoc Multiset.bind_assocₓ'. -/
theorem bind_assoc {s : Multiset α} {f : α → Multiset β} {g : β → Multiset γ} :
    (s.bind f).bind g = s.bind fun a => (f a).bind g :=
  Multiset.induction_on s (by simp) (by simp (config := { contextual := true }))
#align multiset.bind_assoc Multiset.bind_assoc

/- warning: multiset.bind_bind -> Multiset.bind_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (m : Multiset.{u1} α) (n : Multiset.{u2} β) {f : α -> β -> (Multiset.{u3} γ)}, Eq.{succ u3} (Multiset.{u3} γ) (Multiset.bind.{u1, u3} α γ m (fun (a : α) => Multiset.bind.{u2, u3} β γ n (fun (b : β) => f a b))) (Multiset.bind.{u2, u3} β γ n (fun (b : β) => Multiset.bind.{u1, u3} α γ m (fun (a : α) => f a b)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (m : Multiset.{u3} α) (n : Multiset.{u2} β) {f : α -> β -> (Multiset.{u1} γ)}, Eq.{succ u1} (Multiset.{u1} γ) (Multiset.bind.{u3, u1} α γ m (fun (a : α) => Multiset.bind.{u2, u1} β γ n (fun (b : β) => f a b))) (Multiset.bind.{u2, u1} β γ n (fun (b : β) => Multiset.bind.{u3, u1} α γ m (fun (a : α) => f a b)))
Case conversion may be inaccurate. Consider using '#align multiset.bind_bind Multiset.bind_bindₓ'. -/
theorem bind_bind (m : Multiset α) (n : Multiset β) {f : α → β → Multiset γ} :
    (bind m fun a => bind n fun b => f a b) = bind n fun b => bind m fun a => f a b :=
  Multiset.induction_on m (by simp) (by simp (config := { contextual := true }))
#align multiset.bind_bind Multiset.bind_bind

/- warning: multiset.bind_map_comm -> Multiset.bind_map_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (m : Multiset.{u1} α) (n : Multiset.{u2} β) {f : α -> β -> γ}, Eq.{succ u3} (Multiset.{u3} γ) (Multiset.bind.{u1, u3} α γ m (fun (a : α) => Multiset.map.{u2, u3} β γ (fun (b : β) => f a b) n)) (Multiset.bind.{u2, u3} β γ n (fun (b : β) => Multiset.map.{u1, u3} α γ (fun (a : α) => f a b) m))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (m : Multiset.{u3} α) (n : Multiset.{u2} β) {f : α -> β -> γ}, Eq.{succ u1} (Multiset.{u1} γ) (Multiset.bind.{u3, u1} α γ m (fun (a : α) => Multiset.map.{u2, u1} β γ (fun (b : β) => f a b) n)) (Multiset.bind.{u2, u1} β γ n (fun (b : β) => Multiset.map.{u3, u1} α γ (fun (a : α) => f a b) m))
Case conversion may be inaccurate. Consider using '#align multiset.bind_map_comm Multiset.bind_map_commₓ'. -/
theorem bind_map_comm (m : Multiset α) (n : Multiset β) {f : α → β → γ} :
    (bind m fun a => n.map fun b => f a b) = bind n fun b => m.map fun a => f a b :=
  Multiset.induction_on m (by simp) (by simp (config := { contextual := true }))
#align multiset.bind_map_comm Multiset.bind_map_comm

#print Multiset.prod_bind /-
@[simp, to_additive]
theorem prod_bind [CommMonoid β] (s : Multiset α) (t : α → Multiset β) :
    (s.bind t).Prod = (s.map fun a => (t a).Prod).Prod :=
  Multiset.induction_on s (by simp) fun a s ih => by simp [ih, cons_bind]
#align multiset.prod_bind Multiset.prod_bind
-/

/- warning: multiset.rel_bind -> Multiset.rel_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {r : α -> β -> Prop} {p : γ -> δ -> Prop} {s : Multiset.{u1} α} {t : Multiset.{u2} β} {f : α -> (Multiset.{u3} γ)} {g : β -> (Multiset.{u4} δ)}, (Relator.LiftFun.{succ u1, succ u2, succ u3, succ u4} α β (Multiset.{u3} γ) (Multiset.{u4} δ) r (Multiset.Rel.{u3, u4} γ δ p) f g) -> (Multiset.Rel.{u1, u2} α β r s t) -> (Multiset.Rel.{u3, u4} γ δ p (Multiset.bind.{u1, u3} α γ s f) (Multiset.bind.{u2, u4} β δ t g))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} {r : α -> β -> Prop} {p : γ -> δ -> Prop} {s : Multiset.{u4} α} {t : Multiset.{u3} β} {f : α -> (Multiset.{u2} γ)} {g : β -> (Multiset.{u1} δ)}, (Relator.LiftFun.{succ u4, succ u3, succ u2, succ u1} α β (Multiset.{u2} γ) (Multiset.{u1} δ) r (Multiset.Rel.{u2, u1} γ δ p) f g) -> (Multiset.Rel.{u4, u3} α β r s t) -> (Multiset.Rel.{u2, u1} γ δ p (Multiset.bind.{u4, u2} α γ s f) (Multiset.bind.{u3, u1} β δ t g))
Case conversion may be inaccurate. Consider using '#align multiset.rel_bind Multiset.rel_bindₓ'. -/
theorem rel_bind {r : α → β → Prop} {p : γ → δ → Prop} {s t} {f : α → Multiset γ}
    {g : β → Multiset δ} (h : (r ⇒ Rel p) f g) (hst : Rel r s t) : Rel p (s.bind f) (t.bind g) :=
  by
  apply rel_join
  rw [rel_map]
  exact hst.mono fun a ha b hb hr => h hr
#align multiset.rel_bind Multiset.rel_bind

/- warning: multiset.count_sum -> Multiset.count_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] {m : Multiset.{u2} β} {f : β -> (Multiset.{u1} α)} {a : α}, Eq.{1} Nat (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a (Multiset.sum.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)) (Multiset.map.{u2, u1} β (Multiset.{u1} α) f m))) (Multiset.sum.{0} Nat Nat.addCommMonoid (Multiset.map.{u2, 0} β Nat (fun (b : β) => Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a (f b)) m))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] {m : Multiset.{u1} β} {f : β -> (Multiset.{u2} α)} {a : α}, Eq.{1} Nat (Multiset.count.{u2} α (fun (a : α) (b : α) => _inst_1 a b) a (Multiset.sum.{u2} (Multiset.{u2} α) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)) (Multiset.map.{u1, u2} β (Multiset.{u2} α) f m))) (Multiset.sum.{0} Nat Nat.addCommMonoid (Multiset.map.{u1, 0} β Nat (fun (b : β) => Multiset.count.{u2} α (fun (a : α) (b : α) => _inst_1 a b) a (f b)) m))
Case conversion may be inaccurate. Consider using '#align multiset.count_sum Multiset.count_sumₓ'. -/
theorem count_sum [DecidableEq α] {m : Multiset β} {f : β → Multiset α} {a : α} :
    count a (map f m).Sum = sum (m.map fun b => count a <| f b) :=
  Multiset.induction_on m (by simp) (by simp)
#align multiset.count_sum Multiset.count_sum

/- warning: multiset.count_bind -> Multiset.count_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] {m : Multiset.{u2} β} {f : β -> (Multiset.{u1} α)} {a : α}, Eq.{1} Nat (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a (Multiset.bind.{u2, u1} β α m f)) (Multiset.sum.{0} Nat Nat.addCommMonoid (Multiset.map.{u2, 0} β Nat (fun (b : β) => Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a (f b)) m))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] {m : Multiset.{u1} β} {f : β -> (Multiset.{u2} α)} {a : α}, Eq.{1} Nat (Multiset.count.{u2} α (fun (a : α) (b : α) => _inst_1 a b) a (Multiset.bind.{u1, u2} β α m f)) (Multiset.sum.{0} Nat Nat.addCommMonoid (Multiset.map.{u1, 0} β Nat (fun (b : β) => Multiset.count.{u2} α (fun (a : α) (b : α) => _inst_1 a b) a (f b)) m))
Case conversion may be inaccurate. Consider using '#align multiset.count_bind Multiset.count_bindₓ'. -/
theorem count_bind [DecidableEq α] {m : Multiset β} {f : β → Multiset α} {a : α} :
    count a (bind m f) = sum (m.map fun b => count a <| f b) :=
  count_sum
#align multiset.count_bind Multiset.count_bind

/- warning: multiset.le_bind -> Multiset.le_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> (Multiset.{u2} β)} (S : Multiset.{u1} α) {x : α}, (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x S) -> (LE.le.{u2} (Multiset.{u2} β) (Preorder.toLE.{u2} (Multiset.{u2} β) (PartialOrder.toPreorder.{u2} (Multiset.{u2} β) (Multiset.partialOrder.{u2} β))) (f x) (Multiset.bind.{u1, u2} α β S f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> (Multiset.{u1} β)} (S : Multiset.{u2} α) {x : α}, (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x S) -> (LE.le.{u1} (Multiset.{u1} β) (Preorder.toLE.{u1} (Multiset.{u1} β) (PartialOrder.toPreorder.{u1} (Multiset.{u1} β) (Multiset.instPartialOrderMultiset.{u1} β))) (f x) (Multiset.bind.{u2, u1} α β S f))
Case conversion may be inaccurate. Consider using '#align multiset.le_bind Multiset.le_bindₓ'. -/
theorem le_bind {α β : Type _} {f : α → Multiset β} (S : Multiset α) {x : α} (hx : x ∈ S) :
    f x ≤ S.bind f := by
  classical
    rw [le_iff_count]
    intro a
    rw [count_bind]
    apply le_sum_of_mem
    rw [mem_map]
    exact ⟨x, hx, rfl⟩
#align multiset.le_bind Multiset.le_bind

/- warning: multiset.attach_bind_coe -> Multiset.attach_bind_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Multiset.{u1} α) (f : α -> (Multiset.{u2} β)), Eq.{succ u2} (Multiset.{u2} β) (Multiset.bind.{u1, u2} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) β (Multiset.attach.{u1} α s) (fun (i : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s))))) i))) (Multiset.bind.{u1, u2} α β s f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Multiset.{u2} α) (f : α -> (Multiset.{u1} β)), Eq.{succ u1} (Multiset.{u1} β) (Multiset.bind.{u2, u1} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x s)) β (Multiset.attach.{u2} α s) (fun (i : Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x s)) => f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x s) i))) (Multiset.bind.{u2, u1} α β s f)
Case conversion may be inaccurate. Consider using '#align multiset.attach_bind_coe Multiset.attach_bind_coeₓ'. -/
@[simp]
theorem attach_bind_coe (s : Multiset α) (f : α → Multiset β) :
    (s.attach.bind fun i => f i) = s.bind f :=
  congr_arg join <| attach_map_val' _ _
#align multiset.attach_bind_coe Multiset.attach_bind_coe

end Bind

/-! ### Product of two multisets -/


section Product

variable (a : α) (b : β) (s : Multiset α) (t : Multiset β)

#print Multiset.product /-
/-- The multiplicity of `(a, b)` in `s ×ˢ t` is
  the product of the multiplicity of `a` in `s` and `b` in `t`. -/
def product (s : Multiset α) (t : Multiset β) : Multiset (α × β) :=
  s.bind fun a => t.map <| Prod.mk a
#align multiset.product Multiset.product
-/

-- mathport name: multiset.product
infixr:82
  " ×ˢ " =>-- This notation binds more strongly than (pre)images, unions and intersections.
  Multiset.product

/- warning: multiset.coe_product -> Multiset.coe_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l₁ : List.{u1} α) (l₂ : List.{u2} β), Eq.{succ (max u1 u2)} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.product.{u1, u2} α β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) l₁) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (List.{u2} β) (Multiset.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (List.{u2} β) (Multiset.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (List.{u2} β) (Multiset.{u2} β) (coeBase.{succ u2, succ u2} (List.{u2} β) (Multiset.{u2} β) (Multiset.hasCoe.{u2} β)))) l₂)) ((fun (a : Type.{max u1 u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ (max u1 u2), succ (max u1 u2)} a b] => self.0) (List.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (HasLiftT.mk.{succ (max u1 u2), succ (max u1 u2)} (List.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (CoeTCₓ.coe.{succ (max u1 u2), succ (max u1 u2)} (List.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (coeBase.{succ (max u1 u2), succ (max u1 u2)} (List.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.hasCoe.{max u1 u2} (Prod.{u1, u2} α β))))) (List.product.{u1, u2} α β l₁ l₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (l₁ : List.{u2} α) (l₂ : List.{u1} β), Eq.{max (succ u2) (succ u1)} (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (Multiset.product.{u2, u1} α β (Multiset.ofList.{u2} α l₁) (Multiset.ofList.{u1} β l₂)) (Multiset.ofList.{max u2 u1} (Prod.{u2, u1} α β) (List.product.{u2, u1} α β l₁ l₂))
Case conversion may be inaccurate. Consider using '#align multiset.coe_product Multiset.coe_productₓ'. -/
@[simp]
theorem coe_product (l₁ : List α) (l₂ : List β) : @product α β l₁ l₂ = l₁.product l₂ :=
  by
  rw [product, List.product, ← coe_bind]
  simp
#align multiset.coe_product Multiset.coe_product

/- warning: multiset.zero_product -> Multiset.zero_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (t : Multiset.{u2} β), Eq.{succ (max u1 u2)} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.product.{u1, u2} α β (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α)))) t) (OfNat.ofNat.{max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) 0 (OfNat.mk.{max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) 0 (Zero.zero.{max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.hasZero.{max u1 u2} (Prod.{u1, u2} α β)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (t : Multiset.{u1} β), Eq.{max (succ u2) (succ u1)} (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (Multiset.product.{u2, u1} α β (OfNat.ofNat.{u2} (Multiset.{u2} α) 0 (Zero.toOfNat0.{u2} (Multiset.{u2} α) (Multiset.instZeroMultiset.{u2} α))) t) (OfNat.ofNat.{max u2 u1} (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) 0 (Zero.toOfNat0.{max u2 u1} (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (Multiset.instZeroMultiset.{max u2 u1} (Prod.{u2, u1} α β))))
Case conversion may be inaccurate. Consider using '#align multiset.zero_product Multiset.zero_productₓ'. -/
@[simp]
theorem zero_product : @product α β 0 t = 0 :=
  rfl
#align multiset.zero_product Multiset.zero_product

/- warning: multiset.cons_product -> Multiset.cons_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (a : α) (s : Multiset.{u1} α) (t : Multiset.{u2} β), Eq.{succ (max u1 u2)} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.product.{u1, u2} α β (Multiset.cons.{u1} α a s) t) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (instHAdd.{max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.hasAdd.{max u1 u2} (Prod.{u1, u2} α β))) (Multiset.map.{u2, max u1 u2} β (Prod.{u1, u2} α β) (Prod.mk.{u1, u2} α β a) t) (Multiset.product.{u1, u2} α β s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (a : α) (s : Multiset.{u2} α) (t : Multiset.{u1} β), Eq.{max (succ u2) (succ u1)} (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (Multiset.product.{u2, u1} α β (Multiset.cons.{u2} α a s) t) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (instHAdd.{max u2 u1} (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (Multiset.instAddMultiset.{max u2 u1} (Prod.{u2, u1} α β))) (Multiset.map.{u1, max u1 u2} β (Prod.{u2, u1} α β) (Prod.mk.{u2, u1} α β a) t) (Multiset.product.{u2, u1} α β s t))
Case conversion may be inaccurate. Consider using '#align multiset.cons_product Multiset.cons_productₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem cons_product : (a ::ₘ s) ×ˢ t = map (Prod.mk a) t + s ×ˢ t := by simp [product]
#align multiset.cons_product Multiset.cons_product

/- warning: multiset.product_zero -> Multiset.product_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Multiset.{u1} α), Eq.{succ (max u1 u2)} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.product.{u1, u2} α β s (OfNat.ofNat.{u2} (Multiset.{u2} β) 0 (OfNat.mk.{u2} (Multiset.{u2} β) 0 (Zero.zero.{u2} (Multiset.{u2} β) (Multiset.hasZero.{u2} β))))) (OfNat.ofNat.{max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) 0 (OfNat.mk.{max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) 0 (Zero.zero.{max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.hasZero.{max u1 u2} (Prod.{u1, u2} α β)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Multiset.{u2} α), Eq.{max (succ u2) (succ u1)} (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (Multiset.product.{u2, u1} α β s (OfNat.ofNat.{u1} (Multiset.{u1} β) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} β) (Multiset.instZeroMultiset.{u1} β)))) (OfNat.ofNat.{max u2 u1} (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) 0 (Zero.toOfNat0.{max u2 u1} (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (Multiset.instZeroMultiset.{max u2 u1} (Prod.{u2, u1} α β))))
Case conversion may be inaccurate. Consider using '#align multiset.product_zero Multiset.product_zeroₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem product_zero : s ×ˢ (0 : Multiset β) = 0 := by simp [product]
#align multiset.product_zero Multiset.product_zero

/- warning: multiset.product_cons -> Multiset.product_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (b : β) (s : Multiset.{u1} α) (t : Multiset.{u2} β), Eq.{succ (max u1 u2)} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.product.{u1, u2} α β s (Multiset.cons.{u2} β b t)) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (instHAdd.{max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.hasAdd.{max u1 u2} (Prod.{u1, u2} α β))) (Multiset.map.{u1, max u1 u2} α (Prod.{u1, u2} α β) (fun (a : α) => Prod.mk.{u1, u2} α β a b) s) (Multiset.product.{u1, u2} α β s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (b : β) (s : Multiset.{u2} α) (t : Multiset.{u1} β), Eq.{max (succ u2) (succ u1)} (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (Multiset.product.{u2, u1} α β s (Multiset.cons.{u1} β b t)) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (instHAdd.{max u2 u1} (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (Multiset.instAddMultiset.{max u2 u1} (Prod.{u2, u1} α β))) (Multiset.map.{u2, max u1 u2} α (Prod.{u2, u1} α β) (fun (a : α) => Prod.mk.{u2, u1} α β a b) s) (Multiset.product.{u2, u1} α β s t))
Case conversion may be inaccurate. Consider using '#align multiset.product_cons Multiset.product_consₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem product_cons : s ×ˢ (b ::ₘ t) = (s.map fun a => (a, b)) + s ×ˢ t := by simp [product]
#align multiset.product_cons Multiset.product_cons

/- warning: multiset.product_singleton -> Multiset.product_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (a : α) (b : β), Eq.{succ (max u1 u2)} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.product.{u1, u2} α β (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.hasSingleton.{u1} α) a) (Singleton.singleton.{u2, u2} β (Multiset.{u2} β) (Multiset.hasSingleton.{u2} β) b)) (Singleton.singleton.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.hasSingleton.{max u1 u2} (Prod.{u1, u2} α β)) (Prod.mk.{u1, u2} α β a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (a : α) (b : β), Eq.{max (succ u2) (succ u1)} (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (Multiset.product.{u2, u1} α β (Singleton.singleton.{u2, u2} α (Multiset.{u2} α) (Multiset.instSingletonMultiset.{u2} α) a) (Singleton.singleton.{u1, u1} β (Multiset.{u1} β) (Multiset.instSingletonMultiset.{u1} β) b)) (Singleton.singleton.{max u1 u2, max u2 u1} (Prod.{u2, u1} α β) (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (Multiset.instSingletonMultiset.{max u2 u1} (Prod.{u2, u1} α β)) (Prod.mk.{u2, u1} α β a b))
Case conversion may be inaccurate. Consider using '#align multiset.product_singleton Multiset.product_singletonₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem product_singleton : ({a} : Multiset α) ×ˢ ({b} : Multiset β) = {(a, b)} := by
  simp only [product, bind_singleton, map_singleton]
#align multiset.product_singleton Multiset.product_singleton

/- warning: multiset.add_product -> Multiset.add_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Multiset.{u1} α) (t : Multiset.{u1} α) (u : Multiset.{u2} β), Eq.{succ (max u1 u2)} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.product.{u1, u2} α β (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.hasAdd.{u1} α)) s t) u) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (instHAdd.{max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.hasAdd.{max u1 u2} (Prod.{u1, u2} α β))) (Multiset.product.{u1, u2} α β s u) (Multiset.product.{u1, u2} α β t u))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Multiset.{u2} α) (t : Multiset.{u2} α) (u : Multiset.{u1} β), Eq.{max (succ u2) (succ u1)} (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (Multiset.product.{u2, u1} α β (HAdd.hAdd.{u2, u2, u2} (Multiset.{u2} α) (Multiset.{u2} α) (Multiset.{u2} α) (instHAdd.{u2} (Multiset.{u2} α) (Multiset.instAddMultiset.{u2} α)) s t) u) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (instHAdd.{max u2 u1} (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (Multiset.instAddMultiset.{max u2 u1} (Prod.{u2, u1} α β))) (Multiset.product.{u2, u1} α β s u) (Multiset.product.{u2, u1} α β t u))
Case conversion may be inaccurate. Consider using '#align multiset.add_product Multiset.add_productₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem add_product (s t : Multiset α) (u : Multiset β) : (s + t) ×ˢ u = s ×ˢ u + t ×ˢ u := by
  simp [product]
#align multiset.add_product Multiset.add_product

/- warning: multiset.product_add -> Multiset.product_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Multiset.{u1} α) (t : Multiset.{u2} β) (u : Multiset.{u2} β), Eq.{succ (max u1 u2)} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.product.{u1, u2} α β s (HAdd.hAdd.{u2, u2, u2} (Multiset.{u2} β) (Multiset.{u2} β) (Multiset.{u2} β) (instHAdd.{u2} (Multiset.{u2} β) (Multiset.hasAdd.{u2} β)) t u)) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (instHAdd.{max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.hasAdd.{max u1 u2} (Prod.{u1, u2} α β))) (Multiset.product.{u1, u2} α β s t) (Multiset.product.{u1, u2} α β s u))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Multiset.{u2} α) (t : Multiset.{u1} β) (u : Multiset.{u1} β), Eq.{max (succ u2) (succ u1)} (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (Multiset.product.{u2, u1} α β s (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} β) (Multiset.{u1} β) (Multiset.{u1} β) (instHAdd.{u1} (Multiset.{u1} β) (Multiset.instAddMultiset.{u1} β)) t u)) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (instHAdd.{max u2 u1} (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (Multiset.instAddMultiset.{max u2 u1} (Prod.{u2, u1} α β))) (Multiset.product.{u2, u1} α β s t) (Multiset.product.{u2, u1} α β s u))
Case conversion may be inaccurate. Consider using '#align multiset.product_add Multiset.product_addₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem product_add (s : Multiset α) : ∀ t u : Multiset β, s ×ˢ (t + u) = s ×ˢ t + s ×ˢ u :=
  Multiset.induction_on s (fun t u => rfl) fun a s IH t u => by
    rw [cons_product, IH] <;> simp <;> cc
#align multiset.product_add Multiset.product_add

/- warning: multiset.mem_product -> Multiset.mem_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Multiset.{u1} α} {t : Multiset.{u2} β} {p : Prod.{u1, u2} α β}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) p (Multiset.product.{u1, u2} α β s t)) (And (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) (Prod.fst.{u1, u2} α β p) s) (Membership.Mem.{u2, u2} β (Multiset.{u2} β) (Multiset.hasMem.{u2} β) (Prod.snd.{u1, u2} α β p) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Multiset.{u2} α} {t : Multiset.{u1} β} {p : Prod.{u2, u1} α β}, Iff (Membership.mem.{max u2 u1, max u2 u1} (Prod.{u2, u1} α β) (Multiset.{max u1 u2} (Prod.{u2, u1} α β)) (Multiset.instMembershipMultiset.{max u2 u1} (Prod.{u2, u1} α β)) p (Multiset.product.{u2, u1} α β s t)) (And (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) (Prod.fst.{u2, u1} α β p) s) (Membership.mem.{u1, u1} β (Multiset.{u1} β) (Multiset.instMembershipMultiset.{u1} β) (Prod.snd.{u2, u1} α β p) t))
Case conversion may be inaccurate. Consider using '#align multiset.mem_product Multiset.mem_productₓ'. -/
@[simp]
theorem mem_product {s t} : ∀ {p : α × β}, p ∈ @product α β s t ↔ p.1 ∈ s ∧ p.2 ∈ t
  | (a, b) => by simp [product, and_left_comm]
#align multiset.mem_product Multiset.mem_product

/- warning: multiset.card_product -> Multiset.card_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Multiset.{u1} α) (t : Multiset.{u2} β), Eq.{1} Nat (coeFn.{succ (max u1 u2), succ (max u1 u2)} (AddMonoidHom.{max u1 u2, 0} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) Nat (AddMonoid.toAddZeroClass.{max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (AddRightCancelMonoid.toAddMonoid.{max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (AddCancelMonoid.toAddRightCancelMonoid.{max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (AddCancelCommMonoid.toCancelAddMonoid.{max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.orderedCancelAddCommMonoid.{max u1 u2} (Prod.{u1, u2} α β))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{max u1 u2, 0} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) Nat (AddMonoid.toAddZeroClass.{max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (AddRightCancelMonoid.toAddMonoid.{max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (AddCancelMonoid.toAddRightCancelMonoid.{max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (AddCancelCommMonoid.toCancelAddMonoid.{max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.orderedCancelAddCommMonoid.{max u1 u2} (Prod.{u1, u2} α β))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) -> Nat) (AddMonoidHom.hasCoeToFun.{max u1 u2, 0} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) Nat (AddMonoid.toAddZeroClass.{max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (AddRightCancelMonoid.toAddMonoid.{max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (AddCancelMonoid.toAddRightCancelMonoid.{max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (AddCancelCommMonoid.toCancelAddMonoid.{max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u1 u2} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.orderedCancelAddCommMonoid.{max u1 u2} (Prod.{u1, u2} α β))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{max u1 u2} (Prod.{u1, u2} α β)) (Multiset.product.{u1, u2} α β s t)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s) (coeFn.{succ u2, succ u2} (AddMonoidHom.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toCancelAddMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toCancelAddMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u2} β) -> Nat) (AddMonoidHom.hasCoeToFun.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toCancelAddMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.orderedCancelAddCommMonoid.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u2} β) t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Multiset.{u1} α) (t : Multiset.{u2} β), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{max u2 u1} (Prod.{u1, u2} α β)) => Nat) (Multiset.product.{u1, u2} α β s t)) (FunLike.coe.{succ (max u2 u1), succ (max u2 u1), 1} (AddMonoidHom.{max u2 u1, 0} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) Nat (AddMonoid.toAddZeroClass.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (AddRightCancelMonoid.toAddMonoid.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (AddCancelMonoid.toAddRightCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (AddCancelCommMonoid.toAddCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{max u2 u1} (Prod.{u1, u2} α β))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (fun (_x : Multiset.{max u2 u1} (Prod.{u1, u2} α β)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{max u2 u1} (Prod.{u1, u2} α β)) => Nat) _x) (AddHomClass.toFunLike.{max u2 u1, max u2 u1, 0} (AddMonoidHom.{max u2 u1, 0} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) Nat (AddMonoid.toAddZeroClass.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (AddRightCancelMonoid.toAddMonoid.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (AddCancelMonoid.toAddRightCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (AddCancelCommMonoid.toAddCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{max u2 u1} (Prod.{u1, u2} α β))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) Nat (AddZeroClass.toAdd.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (AddMonoid.toAddZeroClass.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (AddRightCancelMonoid.toAddMonoid.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (AddCancelMonoid.toAddRightCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (AddCancelCommMonoid.toAddCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{max u2 u1} (Prod.{u1, u2} α β)))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{max u2 u1, max u2 u1, 0} (AddMonoidHom.{max u2 u1, 0} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) Nat (AddMonoid.toAddZeroClass.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (AddRightCancelMonoid.toAddMonoid.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (AddCancelMonoid.toAddRightCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (AddCancelCommMonoid.toAddCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{max u2 u1} (Prod.{u1, u2} α β))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) Nat (AddMonoid.toAddZeroClass.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (AddRightCancelMonoid.toAddMonoid.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (AddCancelMonoid.toAddRightCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (AddCancelCommMonoid.toAddCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{max u2 u1} (Prod.{u1, u2} α β))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{max u2 u1, 0} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) Nat (AddMonoid.toAddZeroClass.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (AddRightCancelMonoid.toAddMonoid.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (AddCancelMonoid.toAddRightCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (AddCancelCommMonoid.toAddCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u2 u1} (Multiset.{max u2 u1} (Prod.{u1, u2} α β)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{max u2 u1} (Prod.{u1, u2} α β))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{max u2 u1} (Prod.{u1, u2} α β)) (Multiset.product.{u1, u2} α β s t)) (HMul.hMul.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} β) => Nat) t) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) (instHMul.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) instMulNat) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s) (FunLike.coe.{succ u2, succ u2, 1} (AddMonoidHom.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} β) (fun (_x : Multiset.{u2} β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u2} β) => Nat) _x) (AddHomClass.toFunLike.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} β) Nat (AddZeroClass.toAdd.{u2} (Multiset.{u2} β) (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} β))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u2, u2, 0} (AddMonoidHom.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u2, 0} (Multiset.{u2} β) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} β) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} β) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} β) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} β) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} β)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u2} β) t))
Case conversion may be inaccurate. Consider using '#align multiset.card_product Multiset.card_productₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem card_product : (s ×ˢ t).card = s.card * t.card := by simp [product]
#align multiset.card_product Multiset.card_product

end Product

/-! ### Disjoint sum of multisets -/


section Sigma

variable {σ : α → Type _} (a : α) (s : Multiset α) (t : ∀ a, Multiset (σ a))

#print Multiset.sigma /-
/-- `sigma s t` is the dependent version of `product`. It is the sum of
  `(a, b)` as `a` ranges over `s` and `b` ranges over `t a`. -/
protected def sigma (s : Multiset α) (t : ∀ a, Multiset (σ a)) : Multiset (Σa, σ a) :=
  s.bind fun a => (t a).map <| Sigma.mk a
#align multiset.sigma Multiset.sigma
-/

/- warning: multiset.coe_sigma -> Multiset.coe_sigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : α -> Type.{u2}} (l₁ : List.{u1} α) (l₂ : forall (a : α), List.{u2} (σ a)), Eq.{succ (max u1 u2)} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (Multiset.sigma.{u1, u2} α σ ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) l₁) (fun (a : α) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (List.{u2} (σ a)) (Multiset.{u2} (σ a)) (HasLiftT.mk.{succ u2, succ u2} (List.{u2} (σ a)) (Multiset.{u2} (σ a)) (CoeTCₓ.coe.{succ u2, succ u2} (List.{u2} (σ a)) (Multiset.{u2} (σ a)) (coeBase.{succ u2, succ u2} (List.{u2} (σ a)) (Multiset.{u2} (σ a)) (Multiset.hasCoe.{u2} (σ a))))) (l₂ a))) ((fun (a : Type.{max u1 u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ (max u1 u2), succ (max u1 u2)} a b] => self.0) (List.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (HasLiftT.mk.{succ (max u1 u2), succ (max u1 u2)} (List.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (CoeTCₓ.coe.{succ (max u1 u2), succ (max u1 u2)} (List.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (coeBase.{succ (max u1 u2), succ (max u1 u2)} (List.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (Multiset.hasCoe.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a)))))) (List.sigma.{u1, u2} α (fun (a : α) => σ a) l₁ l₂))
but is expected to have type
  forall {α : Type.{u2}} {σ : α -> Type.{u1}} (l₁ : List.{u2} α) (l₂ : forall (a : α), List.{u1} (σ a)), Eq.{max (succ u2) (succ u1)} (Multiset.{max u1 u2} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (Multiset.sigma.{u2, u1} α σ (Multiset.ofList.{u2} α l₁) (fun (a : α) => Multiset.ofList.{u1} (σ a) (l₂ a))) (Multiset.ofList.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a)) (List.sigma.{u2, u1} α (fun (a : α) => σ a) l₁ l₂))
Case conversion may be inaccurate. Consider using '#align multiset.coe_sigma Multiset.coe_sigmaₓ'. -/
@[simp]
theorem coe_sigma (l₁ : List α) (l₂ : ∀ a, List (σ a)) :
    (@Multiset.sigma α σ l₁ fun a => l₂ a) = l₁.Sigma l₂ := by
  rw [Multiset.sigma, List.sigma, ← coe_bind] <;> simp
#align multiset.coe_sigma Multiset.coe_sigma

/- warning: multiset.zero_sigma -> Multiset.zero_sigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : α -> Type.{u2}} (t : forall (a : α), Multiset.{u2} (σ a)), Eq.{succ (max u1 u2)} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (Multiset.sigma.{u1, u2} α σ (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α)))) t) (OfNat.ofNat.{max u1 u2} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) 0 (OfNat.mk.{max u1 u2} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) 0 (Zero.zero.{max u1 u2} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (Multiset.hasZero.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))))))
but is expected to have type
  forall {α : Type.{u2}} {σ : α -> Type.{u1}} (t : forall (a : α), Multiset.{u1} (σ a)), Eq.{max (succ u2) (succ u1)} (Multiset.{max u1 u2} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (Multiset.sigma.{u2, u1} α σ (OfNat.ofNat.{u2} (Multiset.{u2} α) 0 (Zero.toOfNat0.{u2} (Multiset.{u2} α) (Multiset.instZeroMultiset.{u2} α))) t) (OfNat.ofNat.{max u2 u1} (Multiset.{max u1 u2} (Sigma.{u2, u1} α (fun (a : α) => σ a))) 0 (Zero.toOfNat0.{max u2 u1} (Multiset.{max u1 u2} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (Multiset.instZeroMultiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a)))))
Case conversion may be inaccurate. Consider using '#align multiset.zero_sigma Multiset.zero_sigmaₓ'. -/
@[simp]
theorem zero_sigma : @Multiset.sigma α σ 0 t = 0 :=
  rfl
#align multiset.zero_sigma Multiset.zero_sigma

/- warning: multiset.cons_sigma -> Multiset.cons_sigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : α -> Type.{u2}} (a : α) (s : Multiset.{u1} α) (t : forall (a : α), Multiset.{u2} (σ a)), Eq.{succ (max u1 u2)} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (Multiset.sigma.{u1, u2} α (fun (a : α) => σ a) (Multiset.cons.{u1} α a s) t) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (instHAdd.{max u1 u2} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (Multiset.hasAdd.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a)))) (Multiset.map.{u2, max u1 u2} (σ a) (Sigma.{u1, u2} α (fun (a : α) => σ a)) (Sigma.mk.{u1, u2} α σ a) (t a)) (Multiset.sigma.{u1, u2} α (fun (a : α) => σ a) s t))
but is expected to have type
  forall {α : Type.{u2}} {σ : α -> Type.{u1}} (a : α) (s : Multiset.{u2} α) (t : forall (a : α), Multiset.{u1} (σ a)), Eq.{max (succ u2) (succ u1)} (Multiset.{max u1 u2} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (Multiset.sigma.{u2, u1} α (fun (a : α) => σ a) (Multiset.cons.{u2} α a s) t) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α σ)) (Multiset.{max u1 u2} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (Multiset.{max u2 u1} (Sigma.{u2, u1} α σ)) (instHAdd.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α σ)) (Multiset.instAddMultiset.{max u2 u1} (Sigma.{u2, u1} α σ))) (Multiset.map.{u1, max u2 u1} (σ a) (Sigma.{u2, u1} α σ) (Sigma.mk.{u2, u1} α σ a) (t a)) (Multiset.sigma.{u2, u1} α (fun (a : α) => σ a) s t))
Case conversion may be inaccurate. Consider using '#align multiset.cons_sigma Multiset.cons_sigmaₓ'. -/
@[simp]
theorem cons_sigma : (a ::ₘ s).Sigma t = (t a).map (Sigma.mk a) + s.Sigma t := by
  simp [Multiset.sigma]
#align multiset.cons_sigma Multiset.cons_sigma

/- warning: multiset.sigma_singleton -> Multiset.sigma_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (a : α) (b : α -> β), Eq.{succ (max u1 u2)} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β))) (Multiset.sigma.{u1, u2} α (fun (a : α) => β) (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.hasSingleton.{u1} α) a) (fun (a : α) => Singleton.singleton.{u2, u2} β (Multiset.{u2} β) (Multiset.hasSingleton.{u2} β) (b a))) (Singleton.singleton.{max u1 u2, max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β)) (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β))) (Multiset.hasSingleton.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β))) (Sigma.mk.{u1, u2} α (fun (a : α) => β) a (b a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (a : α) (b : α -> β), Eq.{max (succ u2) (succ u1)} (Multiset.{max u1 u2} (Sigma.{u2, u1} α (fun (a : α) => β))) (Multiset.sigma.{u2, u1} α (fun (a : α) => β) (Singleton.singleton.{u2, u2} α (Multiset.{u2} α) (Multiset.instSingletonMultiset.{u2} α) a) (fun (a : α) => Singleton.singleton.{u1, u1} β (Multiset.{u1} β) (Multiset.instSingletonMultiset.{u1} β) (b a))) (Singleton.singleton.{max u2 u1, max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => β)) (Multiset.{max u1 u2} (Sigma.{u2, u1} α (fun (a : α) => β))) (Multiset.instSingletonMultiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => β))) (Sigma.mk.{u2, u1} α (fun (a : α) => β) a (b a)))
Case conversion may be inaccurate. Consider using '#align multiset.sigma_singleton Multiset.sigma_singletonₓ'. -/
@[simp]
theorem sigma_singleton (b : α → β) :
    (({a} : Multiset α).Sigma fun a => ({b a} : Multiset β)) = {⟨a, b a⟩} :=
  rfl
#align multiset.sigma_singleton Multiset.sigma_singleton

/- warning: multiset.add_sigma -> Multiset.add_sigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : α -> Type.{u2}} (s : Multiset.{u1} α) (t : Multiset.{u1} α) (u : forall (a : α), Multiset.{u2} (σ a)), Eq.{succ (max u1 u2)} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (Multiset.sigma.{u1, u2} α (fun (a : α) => σ a) (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.hasAdd.{u1} α)) s t) u) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (instHAdd.{max u1 u2} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (Multiset.hasAdd.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a)))) (Multiset.sigma.{u1, u2} α (fun (a : α) => σ a) s u) (Multiset.sigma.{u1, u2} α (fun (a : α) => σ a) t u))
but is expected to have type
  forall {α : Type.{u2}} {σ : α -> Type.{u1}} (s : Multiset.{u2} α) (t : Multiset.{u2} α) (u : forall (a : α), Multiset.{u1} (σ a)), Eq.{max (succ u2) (succ u1)} (Multiset.{max u1 u2} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (Multiset.sigma.{u2, u1} α (fun (a : α) => σ a) (HAdd.hAdd.{u2, u2, u2} (Multiset.{u2} α) (Multiset.{u2} α) (Multiset.{u2} α) (instHAdd.{u2} (Multiset.{u2} α) (Multiset.instAddMultiset.{u2} α)) s t) u) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Multiset.{max u1 u2} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (Multiset.{max u1 u2} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (Multiset.{max u1 u2} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (instHAdd.{max u2 u1} (Multiset.{max u1 u2} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (Multiset.instAddMultiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a)))) (Multiset.sigma.{u2, u1} α (fun (a : α) => σ a) s u) (Multiset.sigma.{u2, u1} α (fun (a : α) => σ a) t u))
Case conversion may be inaccurate. Consider using '#align multiset.add_sigma Multiset.add_sigmaₓ'. -/
@[simp]
theorem add_sigma (s t : Multiset α) (u : ∀ a, Multiset (σ a)) :
    (s + t).Sigma u = s.Sigma u + t.Sigma u := by simp [Multiset.sigma]
#align multiset.add_sigma Multiset.add_sigma

#print Multiset.sigma_add /-
@[simp]
theorem sigma_add :
    ∀ t u : ∀ a, Multiset (σ a), (s.Sigma fun a => t a + u a) = s.Sigma t + s.Sigma u :=
  Multiset.induction_on s (fun t u => rfl) fun a s IH t u => by rw [cons_sigma, IH] <;> simp <;> cc
#align multiset.sigma_add Multiset.sigma_add
-/

/- warning: multiset.mem_sigma -> Multiset.mem_sigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : α -> Type.{u2}} {s : Multiset.{u1} α} {t : forall (a : α), Multiset.{u2} (σ a)} {p : Sigma.{u1, u2} α (fun (a : α) => σ a)}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a)) (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (Multiset.hasMem.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) p (Multiset.sigma.{u1, u2} α σ s t)) (And (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) (Sigma.fst.{u1, u2} α (fun (a : α) => σ a) p) s) (Membership.Mem.{u2, u2} (σ (Sigma.fst.{u1, u2} α (fun (a : α) => σ a) p)) (Multiset.{u2} (σ (Sigma.fst.{u1, u2} α (fun (a : α) => σ a) p))) (Multiset.hasMem.{u2} (σ (Sigma.fst.{u1, u2} α (fun (a : α) => σ a) p))) (Sigma.snd.{u1, u2} α (fun (a : α) => σ a) p) (t (Sigma.fst.{u1, u2} α (fun (a : α) => σ a) p))))
but is expected to have type
  forall {α : Type.{u2}} {σ : α -> Type.{u1}} {s : Multiset.{u2} α} {t : forall (a : α), Multiset.{u1} (σ a)} {p : Sigma.{u2, u1} α (fun (a : α) => σ a)}, Iff (Membership.mem.{max u2 u1, max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a)) (Multiset.{max u1 u2} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (Multiset.instMembershipMultiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) p (Multiset.sigma.{u2, u1} α σ s t)) (And (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) (Sigma.fst.{u2, u1} α (fun (a : α) => σ a) p) s) (Membership.mem.{u1, u1} (σ (Sigma.fst.{u2, u1} α (fun (a : α) => σ a) p)) (Multiset.{u1} (σ (Sigma.fst.{u2, u1} α (fun (a : α) => σ a) p))) (Multiset.instMembershipMultiset.{u1} (σ (Sigma.fst.{u2, u1} α (fun (a : α) => σ a) p))) (Sigma.snd.{u2, u1} α (fun (a : α) => σ a) p) (t (Sigma.fst.{u2, u1} α (fun (a : α) => σ a) p))))
Case conversion may be inaccurate. Consider using '#align multiset.mem_sigma Multiset.mem_sigmaₓ'. -/
@[simp]
theorem mem_sigma {s t} : ∀ {p : Σa, σ a}, p ∈ @Multiset.sigma α σ s t ↔ p.1 ∈ s ∧ p.2 ∈ t p.1
  | ⟨a, b⟩ => by simp [Multiset.sigma, and_assoc', and_left_comm]
#align multiset.mem_sigma Multiset.mem_sigma

/- warning: multiset.card_sigma -> Multiset.card_sigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : α -> Type.{u2}} (s : Multiset.{u1} α) (t : forall (a : α), Multiset.{u2} (σ a)), Eq.{1} Nat (coeFn.{succ (max u1 u2), succ (max u1 u2)} (AddMonoidHom.{max u1 u2, 0} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) Nat (AddMonoid.toAddZeroClass.{max u1 u2} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (AddRightCancelMonoid.toAddMonoid.{max u1 u2} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (AddCancelMonoid.toAddRightCancelMonoid.{max u1 u2} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (AddCancelCommMonoid.toCancelAddMonoid.{max u1 u2} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u1 u2} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (Multiset.orderedCancelAddCommMonoid.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{max u1 u2, 0} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) Nat (AddMonoid.toAddZeroClass.{max u1 u2} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (AddRightCancelMonoid.toAddMonoid.{max u1 u2} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (AddCancelMonoid.toAddRightCancelMonoid.{max u1 u2} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (AddCancelCommMonoid.toCancelAddMonoid.{max u1 u2} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u1 u2} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (Multiset.orderedCancelAddCommMonoid.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) -> Nat) (AddMonoidHom.hasCoeToFun.{max u1 u2, 0} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) Nat (AddMonoid.toAddZeroClass.{max u1 u2} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (AddRightCancelMonoid.toAddMonoid.{max u1 u2} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (AddCancelMonoid.toAddRightCancelMonoid.{max u1 u2} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (AddCancelCommMonoid.toCancelAddMonoid.{max u1 u2} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u1 u2} (Multiset.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (Multiset.orderedCancelAddCommMonoid.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => σ a))) (Multiset.sigma.{u1, u2} α (fun (a : α) => σ a) s t)) (Multiset.sum.{0} Nat Nat.addCommMonoid (Multiset.map.{u1, 0} α Nat (fun (a : α) => coeFn.{succ u2, succ u2} (AddMonoidHom.{u2, 0} (Multiset.{u2} (σ a)) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} (σ a)) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} (σ a)) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} (σ a)) (AddCancelCommMonoid.toCancelAddMonoid.{u2} (Multiset.{u2} (σ a)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} (σ a)) (Multiset.orderedCancelAddCommMonoid.{u2} (σ a))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u2, 0} (Multiset.{u2} (σ a)) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} (σ a)) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} (σ a)) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} (σ a)) (AddCancelCommMonoid.toCancelAddMonoid.{u2} (Multiset.{u2} (σ a)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} (σ a)) (Multiset.orderedCancelAddCommMonoid.{u2} (σ a))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u2} (σ a)) -> Nat) (AddMonoidHom.hasCoeToFun.{u2, 0} (Multiset.{u2} (σ a)) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} (σ a)) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} (σ a)) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} (σ a)) (AddCancelCommMonoid.toCancelAddMonoid.{u2} (Multiset.{u2} (σ a)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} (σ a)) (Multiset.orderedCancelAddCommMonoid.{u2} (σ a))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u2} (σ a)) (t a)) s))
but is expected to have type
  forall {α : Type.{u2}} {σ : α -> Type.{u1}} (s : Multiset.{u2} α) (t : forall (a : α), Multiset.{u1} (σ a)), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) => Nat) (Multiset.sigma.{u2, u1} α (fun (a : α) => σ a) s t)) (FunLike.coe.{succ (max u2 u1), succ (max u2 u1), 1} (AddMonoidHom.{max u2 u1, 0} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) Nat (AddMonoid.toAddZeroClass.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (AddRightCancelMonoid.toAddMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (AddCancelMonoid.toAddRightCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (AddCancelCommMonoid.toAddCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (Multiset.instOrderedCancelAddCommMonoidMultiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (fun (_x : Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) => Nat) _x) (AddHomClass.toFunLike.{max u2 u1, max u2 u1, 0} (AddMonoidHom.{max u2 u1, 0} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) Nat (AddMonoid.toAddZeroClass.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (AddRightCancelMonoid.toAddMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (AddCancelMonoid.toAddRightCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (AddCancelCommMonoid.toAddCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (Multiset.instOrderedCancelAddCommMonoidMultiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) Nat (AddZeroClass.toAdd.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (AddMonoid.toAddZeroClass.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (AddRightCancelMonoid.toAddMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (AddCancelMonoid.toAddRightCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (AddCancelCommMonoid.toAddCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (Multiset.instOrderedCancelAddCommMonoidMultiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{max u2 u1, max u2 u1, 0} (AddMonoidHom.{max u2 u1, 0} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) Nat (AddMonoid.toAddZeroClass.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (AddRightCancelMonoid.toAddMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (AddCancelMonoid.toAddRightCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (AddCancelCommMonoid.toAddCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (Multiset.instOrderedCancelAddCommMonoidMultiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) Nat (AddMonoid.toAddZeroClass.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (AddRightCancelMonoid.toAddMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (AddCancelMonoid.toAddRightCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (AddCancelCommMonoid.toAddCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (Multiset.instOrderedCancelAddCommMonoidMultiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{max u2 u1, 0} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) Nat (AddMonoid.toAddZeroClass.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (AddRightCancelMonoid.toAddMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (AddCancelMonoid.toAddRightCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (AddCancelCommMonoid.toAddCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u2 u1} (Multiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (Multiset.instOrderedCancelAddCommMonoidMultiset.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => σ a))) (Multiset.sigma.{u2, u1} α (fun (a : α) => σ a) s t)) (Multiset.sum.{0} Nat Nat.addCommMonoid (Multiset.map.{u2, 0} α Nat (fun (a : α) => FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} (σ a)) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (σ a)) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (σ a)) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (σ a)) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (σ a)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (σ a)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (σ a))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} (σ a)) (fun (_x : Multiset.{u1} (σ a)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} (σ a)) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} (σ a)) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (σ a)) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (σ a)) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (σ a)) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (σ a)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (σ a)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (σ a))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} (σ a)) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} (σ a)) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (σ a)) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (σ a)) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (σ a)) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (σ a)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (σ a)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (σ a)))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} (σ a)) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (σ a)) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (σ a)) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (σ a)) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (σ a)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (σ a)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (σ a))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} (σ a)) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (σ a)) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (σ a)) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (σ a)) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (σ a)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (σ a)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (σ a))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} (σ a)) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (σ a)) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (σ a)) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (σ a)) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (σ a)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (σ a)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (σ a))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} (σ a)) (t a)) s))
Case conversion may be inaccurate. Consider using '#align multiset.card_sigma Multiset.card_sigmaₓ'. -/
@[simp]
theorem card_sigma : card (s.Sigma t) = sum (map (fun a => card (t a)) s) := by
  simp [Multiset.sigma, (· ∘ ·)]
#align multiset.card_sigma Multiset.card_sigma

end Sigma

end Multiset

