/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module data.set.semiring
! leanprover-community/mathlib commit 62e8311c791f02c47451bf14aa2501048e7c2f33
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Kleene
import Mathbin.Data.Set.Pointwise.Smul

/-!
# Sets as a semiring under union

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `set_semiring α`, an alias of `set α`, which we endow with `∪` as addition and
pointwise `*` as multiplication. If `α` is a (commutative) monoid, `set_semiring α` is a
(commutative) semiring.
-/


open Function Set

open Pointwise

variable {α β : Type _}

#print SetSemiring /-
/-- An alias for `set α`, which has a semiring structure given by `∪` as "addition" and pointwise
  multiplication `*` as "multiplication". -/
def SetSemiring (α : Type _) : Type _ :=
  Set α deriving Inhabited, PartialOrder, OrderBot
#align set_semiring SetSemiring
-/

#print Set.up /-
/-- The identity function `set α → set_semiring α`. -/
protected def Set.up : Set α ≃ SetSemiring α :=
  Equiv.refl _
#align set.up Set.up
-/

namespace SetSemiring

#print SetSemiring.down /-
/-- The identity function `set_semiring α → set α`. -/
protected def down : SetSemiring α ≃ Set α :=
  Equiv.refl _
#align set_semiring.down SetSemiring.down
-/

#print SetSemiring.down_up /-
@[simp]
protected theorem down_up (s : Set α) : s.up.down = s :=
  rfl
#align set_semiring.down_up SetSemiring.down_up
-/

#print SetSemiring.up_down /-
@[simp]
protected theorem up_down (s : SetSemiring α) : s.down.up = s :=
  rfl
#align set_semiring.up_down SetSemiring.up_down
-/

/- warning: set_semiring.up_le_up -> SetSemiring.up_le_up is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (LE.le.{u1} (SetSemiring.{u1} α) (Preorder.toHasLe.{u1} (SetSemiring.{u1} α) (PartialOrder.toPreorder.{u1} (SetSemiring.{u1} α) (SetSemiring.partialOrder.{u1} α))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) => (Set.{u1} α) -> (SetSemiring.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.up.{u1} α) s) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) => (Set.{u1} α) -> (SetSemiring.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.up.{u1} α) t)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (LE.le.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Set.{u1} α) => SetSemiring.{u1} α) s) (Preorder.toLE.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Set.{u1} α) => SetSemiring.{u1} α) s) (PartialOrder.toPreorder.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Set.{u1} α) => SetSemiring.{u1} α) s) (instPartialOrderSetSemiring.{u1} α))) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.{u1} α) (fun (_x : Set.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Set.{u1} α) => SetSemiring.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.up.{u1} α) s) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.{u1} α) (fun (_x : Set.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Set.{u1} α) => SetSemiring.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.up.{u1} α) t)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set_semiring.up_le_up SetSemiring.up_le_upₓ'. -/
-- TODO: These lemmas are not tagged `simp` because `set.le_eq_subset` simplifies the LHS
theorem up_le_up {s t : Set α} : s.up ≤ t.up ↔ s ⊆ t :=
  Iff.rfl
#align set_semiring.up_le_up SetSemiring.up_le_up

/- warning: set_semiring.up_lt_up -> SetSemiring.up_lt_up is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (LT.lt.{u1} (SetSemiring.{u1} α) (Preorder.toHasLt.{u1} (SetSemiring.{u1} α) (PartialOrder.toPreorder.{u1} (SetSemiring.{u1} α) (SetSemiring.partialOrder.{u1} α))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) => (Set.{u1} α) -> (SetSemiring.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.up.{u1} α) s) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) => (Set.{u1} α) -> (SetSemiring.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.up.{u1} α) t)) (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (LT.lt.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Set.{u1} α) => SetSemiring.{u1} α) s) (Preorder.toLT.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Set.{u1} α) => SetSemiring.{u1} α) s) (PartialOrder.toPreorder.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Set.{u1} α) => SetSemiring.{u1} α) s) (instPartialOrderSetSemiring.{u1} α))) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.{u1} α) (fun (_x : Set.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Set.{u1} α) => SetSemiring.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.up.{u1} α) s) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.{u1} α) (fun (_x : Set.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Set.{u1} α) => SetSemiring.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.up.{u1} α) t)) (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set_semiring.up_lt_up SetSemiring.up_lt_upₓ'. -/
theorem up_lt_up {s t : Set α} : s.up < t.up ↔ s ⊂ t :=
  Iff.rfl
#align set_semiring.up_lt_up SetSemiring.up_lt_up

#print SetSemiring.down_subset_down /-
@[simp]
theorem down_subset_down {s t : SetSemiring α} : s.down ⊆ t.down ↔ s ≤ t :=
  Iff.rfl
#align set_semiring.down_subset_down SetSemiring.down_subset_down
-/

/- warning: set_semiring.down_ssubset_down -> SetSemiring.down_ssubset_down is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : SetSemiring.{u1} α} {t : SetSemiring.{u1} α}, Iff (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) => (SetSemiring.{u1} α) -> (Set.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (SetSemiring.down.{u1} α) s) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) => (SetSemiring.{u1} α) -> (Set.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (SetSemiring.down.{u1} α) t)) (LT.lt.{u1} (SetSemiring.{u1} α) (Preorder.toHasLt.{u1} (SetSemiring.{u1} α) (PartialOrder.toPreorder.{u1} (SetSemiring.{u1} α) (SetSemiring.partialOrder.{u1} α))) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : SetSemiring.{u1} α} {t : SetSemiring.{u1} α}, Iff (HasSSubset.SSubset.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : SetSemiring.{u1} α) => Set.{u1} α) s) (Set.instHasSSubsetSet.{u1} α) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (SetSemiring.{u1} α) (fun (_x : SetSemiring.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : SetSemiring.{u1} α) => Set.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (SetSemiring.down.{u1} α) s) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (SetSemiring.{u1} α) (fun (_x : SetSemiring.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : SetSemiring.{u1} α) => Set.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (SetSemiring.down.{u1} α) t)) (LT.lt.{u1} (SetSemiring.{u1} α) (Preorder.toLT.{u1} (SetSemiring.{u1} α) (PartialOrder.toPreorder.{u1} (SetSemiring.{u1} α) (instPartialOrderSetSemiring.{u1} α))) s t)
Case conversion may be inaccurate. Consider using '#align set_semiring.down_ssubset_down SetSemiring.down_ssubset_downₓ'. -/
@[simp]
theorem down_ssubset_down {s t : SetSemiring α} : s.down ⊂ t.down ↔ s < t :=
  Iff.rfl
#align set_semiring.down_ssubset_down SetSemiring.down_ssubset_down

instance : AddCommMonoid (SetSemiring α)
    where
  add s t := (s.down ∪ t.down).up
  zero := (∅ : Set α).up
  add_assoc := union_assoc
  zero_add := empty_union
  add_zero := union_empty
  add_comm := union_comm

/- warning: set_semiring.zero_def -> SetSemiring.zero_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (SetSemiring.{u1} α) (OfNat.ofNat.{u1} (SetSemiring.{u1} α) 0 (OfNat.mk.{u1} (SetSemiring.{u1} α) 0 (Zero.zero.{u1} (SetSemiring.{u1} α) (AddZeroClass.toHasZero.{u1} (SetSemiring.{u1} α) (AddMonoid.toAddZeroClass.{u1} (SetSemiring.{u1} α) (AddCommMonoid.toAddMonoid.{u1} (SetSemiring.{u1} α) (SetSemiring.addCommMonoid.{u1} α))))))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) => (Set.{u1} α) -> (SetSemiring.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.up.{u1} α) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (SetSemiring.{u1} α) (OfNat.ofNat.{u1} (SetSemiring.{u1} α) 0 (Zero.toOfNat0.{u1} (SetSemiring.{u1} α) (AddMonoid.toZero.{u1} (SetSemiring.{u1} α) (AddCommMonoid.toAddMonoid.{u1} (SetSemiring.{u1} α) (SetSemiring.instAddCommMonoidSetSemiring.{u1} α))))) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.{u1} α) (fun (_x : Set.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Set.{u1} α) => SetSemiring.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.up.{u1} α) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)))
Case conversion may be inaccurate. Consider using '#align set_semiring.zero_def SetSemiring.zero_defₓ'. -/
theorem zero_def : (0 : SetSemiring α) = Set.up ∅ :=
  rfl
#align set_semiring.zero_def SetSemiring.zero_def

#print SetSemiring.down_zero /-
@[simp]
theorem down_zero : (0 : SetSemiring α).down = ∅ :=
  rfl
#align set_semiring.down_zero SetSemiring.down_zero
-/

#print Set.up_empty /-
@[simp]
theorem Set.up_empty : (∅ : Set α).up = 0 :=
  rfl
#align set.up_empty Set.up_empty
-/

/- warning: set_semiring.add_def -> SetSemiring.add_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : SetSemiring.{u1} α) (t : SetSemiring.{u1} α), Eq.{succ u1} (SetSemiring.{u1} α) (HAdd.hAdd.{u1, u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (SetSemiring.{u1} α) (instHAdd.{u1} (SetSemiring.{u1} α) (AddZeroClass.toHasAdd.{u1} (SetSemiring.{u1} α) (AddMonoid.toAddZeroClass.{u1} (SetSemiring.{u1} α) (AddCommMonoid.toAddMonoid.{u1} (SetSemiring.{u1} α) (SetSemiring.addCommMonoid.{u1} α))))) s t) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) => (Set.{u1} α) -> (SetSemiring.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.up.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) => (SetSemiring.{u1} α) -> (Set.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (SetSemiring.down.{u1} α) s) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) => (SetSemiring.{u1} α) -> (Set.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (SetSemiring.down.{u1} α) t)))
but is expected to have type
  forall {α : Type.{u1}} (s : SetSemiring.{u1} α) (t : SetSemiring.{u1} α), Eq.{succ u1} (SetSemiring.{u1} α) (HAdd.hAdd.{u1, u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (SetSemiring.{u1} α) (instHAdd.{u1} (SetSemiring.{u1} α) (AddZeroClass.toAdd.{u1} (SetSemiring.{u1} α) (AddMonoid.toAddZeroClass.{u1} (SetSemiring.{u1} α) (AddCommMonoid.toAddMonoid.{u1} (SetSemiring.{u1} α) (SetSemiring.instAddCommMonoidSetSemiring.{u1} α))))) s t) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.{u1} α) (fun (_x : Set.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Set.{u1} α) => SetSemiring.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.up.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (SetSemiring.{u1} α) (fun (_x : SetSemiring.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : SetSemiring.{u1} α) => Set.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (SetSemiring.down.{u1} α) s) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (SetSemiring.{u1} α) (fun (_x : SetSemiring.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : SetSemiring.{u1} α) => Set.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (SetSemiring.down.{u1} α) t)))
Case conversion may be inaccurate. Consider using '#align set_semiring.add_def SetSemiring.add_defₓ'. -/
theorem add_def (s t : SetSemiring α) : s + t = (s.down ∪ t.down).up :=
  rfl
#align set_semiring.add_def SetSemiring.add_def

#print SetSemiring.down_add /-
@[simp]
theorem down_add (s t : SetSemiring α) : (s + t).down = s.down ∪ t.down :=
  rfl
#align set_semiring.down_add SetSemiring.down_add
-/

#print Set.up_union /-
@[simp]
theorem Set.up_union (s t : Set α) : (s ∪ t).up = s.up + t.up :=
  rfl
#align set.up_union Set.up_union
-/

/- warning: set_semiring.covariant_class_add -> SetSemiring.covariantClass_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, CovariantClass.{u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (HAdd.hAdd.{u1, u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (SetSemiring.{u1} α) (instHAdd.{u1} (SetSemiring.{u1} α) (AddZeroClass.toHasAdd.{u1} (SetSemiring.{u1} α) (AddMonoid.toAddZeroClass.{u1} (SetSemiring.{u1} α) (AddCommMonoid.toAddMonoid.{u1} (SetSemiring.{u1} α) (SetSemiring.addCommMonoid.{u1} α)))))) (LE.le.{u1} (SetSemiring.{u1} α) (Preorder.toHasLe.{u1} (SetSemiring.{u1} α) (PartialOrder.toPreorder.{u1} (SetSemiring.{u1} α) (SetSemiring.partialOrder.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}}, CovariantClass.{u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (fun (x._@.Mathlib.Data.Set.Semiring._hyg.498 : SetSemiring.{u1} α) (x._@.Mathlib.Data.Set.Semiring._hyg.500 : SetSemiring.{u1} α) => HAdd.hAdd.{u1, u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (SetSemiring.{u1} α) (instHAdd.{u1} (SetSemiring.{u1} α) (AddZeroClass.toAdd.{u1} (SetSemiring.{u1} α) (AddMonoid.toAddZeroClass.{u1} (SetSemiring.{u1} α) (AddCommMonoid.toAddMonoid.{u1} (SetSemiring.{u1} α) (SetSemiring.instAddCommMonoidSetSemiring.{u1} α))))) x._@.Mathlib.Data.Set.Semiring._hyg.498 x._@.Mathlib.Data.Set.Semiring._hyg.500) (fun (x._@.Mathlib.Data.Set.Semiring._hyg.513 : SetSemiring.{u1} α) (x._@.Mathlib.Data.Set.Semiring._hyg.515 : SetSemiring.{u1} α) => LE.le.{u1} (SetSemiring.{u1} α) (Preorder.toLE.{u1} (SetSemiring.{u1} α) (PartialOrder.toPreorder.{u1} (SetSemiring.{u1} α) (instPartialOrderSetSemiring.{u1} α))) x._@.Mathlib.Data.Set.Semiring._hyg.513 x._@.Mathlib.Data.Set.Semiring._hyg.515)
Case conversion may be inaccurate. Consider using '#align set_semiring.covariant_class_add SetSemiring.covariantClass_addₓ'. -/
/- Since addition on `set_semiring` is commutative (it is set union), there is no need
to also have the instance `covariant_class (set_semiring α) (set_semiring α) (swap (+)) (≤)`. -/
instance covariantClass_add : CovariantClass (SetSemiring α) (SetSemiring α) (· + ·) (· ≤ ·) :=
  ⟨fun a b c => union_subset_union_right _⟩
#align set_semiring.covariant_class_add SetSemiring.covariantClass_add

section Mul

variable [Mul α]

instance : NonUnitalNonAssocSemiring (SetSemiring α) :=
  {-- reducibility linter complains if we use `(s.down * t.down).up`
    SetSemiring.addCommMonoid with
    mul := fun s t => (image2 (· * ·) s.down t.down).up
    zero_mul := fun s => empty_mul
    mul_zero := fun s => mul_empty
    left_distrib := fun _ _ _ => mul_union
    right_distrib := fun _ _ _ => union_mul }

/- warning: set_semiring.mul_def -> SetSemiring.mul_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] (s : SetSemiring.{u1} α) (t : SetSemiring.{u1} α), Eq.{succ u1} (SetSemiring.{u1} α) (HMul.hMul.{u1, u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (SetSemiring.{u1} α) (instHMul.{u1} (SetSemiring.{u1} α) (Distrib.toHasMul.{u1} (SetSemiring.{u1} α) (NonUnitalNonAssocSemiring.toDistrib.{u1} (SetSemiring.{u1} α) (SetSemiring.nonUnitalNonAssocSemiring.{u1} α _inst_1)))) s t) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) => (Set.{u1} α) -> (SetSemiring.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.up.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) => (SetSemiring.{u1} α) -> (Set.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (SetSemiring.down.{u1} α) s) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) => (SetSemiring.{u1} α) -> (Set.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (SetSemiring.down.{u1} α) t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] (s : SetSemiring.{u1} α) (t : SetSemiring.{u1} α), Eq.{succ u1} (SetSemiring.{u1} α) (HMul.hMul.{u1, u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (SetSemiring.{u1} α) (instHMul.{u1} (SetSemiring.{u1} α) (NonUnitalNonAssocSemiring.toMul.{u1} (SetSemiring.{u1} α) (SetSemiring.instNonUnitalNonAssocSemiringSetSemiring.{u1} α _inst_1))) s t) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.{u1} α) (fun (_x : Set.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Set.{u1} α) => SetSemiring.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.up.{u1} α) (HMul.hMul.{u1, u1, u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : SetSemiring.{u1} α) => Set.{u1} α) s) ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : SetSemiring.{u1} α) => Set.{u1} α) t) ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : SetSemiring.{u1} α) => Set.{u1} α) s) (instHMul.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : SetSemiring.{u1} α) => Set.{u1} α) s) (Set.mul.{u1} α _inst_1)) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (SetSemiring.{u1} α) (fun (_x : SetSemiring.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : SetSemiring.{u1} α) => Set.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (SetSemiring.down.{u1} α) s) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (SetSemiring.{u1} α) (fun (_x : SetSemiring.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : SetSemiring.{u1} α) => Set.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (SetSemiring.down.{u1} α) t)))
Case conversion may be inaccurate. Consider using '#align set_semiring.mul_def SetSemiring.mul_defₓ'. -/
theorem mul_def (s t : SetSemiring α) : s * t = (s.down * t.down).up :=
  rfl
#align set_semiring.mul_def SetSemiring.mul_def

#print SetSemiring.down_mul /-
@[simp]
theorem down_mul (s t : SetSemiring α) : (s * t).down = s.down * t.down :=
  rfl
#align set_semiring.down_mul SetSemiring.down_mul
-/

#print Set.up_mul /-
@[simp]
theorem Set.up_mul (s t : Set α) : (s * t).up = s.up * t.up :=
  rfl
#align set.up_mul Set.up_mul
-/

instance : NoZeroDivisors (SetSemiring α) :=
  ⟨fun a b ab =>
    a.eq_empty_or_nonempty.imp_right fun ha =>
      b.eq_empty_or_nonempty.resolve_right fun hb =>
        Nonempty.ne_empty ⟨_, mul_mem_mul ha.some_mem hb.some_mem⟩ ab⟩

/- warning: set_semiring.covariant_class_mul_left -> SetSemiring.covariantClass_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α], CovariantClass.{u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (HMul.hMul.{u1, u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (SetSemiring.{u1} α) (instHMul.{u1} (SetSemiring.{u1} α) (Distrib.toHasMul.{u1} (SetSemiring.{u1} α) (NonUnitalNonAssocSemiring.toDistrib.{u1} (SetSemiring.{u1} α) (SetSemiring.nonUnitalNonAssocSemiring.{u1} α _inst_1))))) (LE.le.{u1} (SetSemiring.{u1} α) (Preorder.toHasLe.{u1} (SetSemiring.{u1} α) (PartialOrder.toPreorder.{u1} (SetSemiring.{u1} α) (SetSemiring.partialOrder.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α], CovariantClass.{u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (fun (x._@.Mathlib.Data.Set.Semiring._hyg.786 : SetSemiring.{u1} α) (x._@.Mathlib.Data.Set.Semiring._hyg.788 : SetSemiring.{u1} α) => HMul.hMul.{u1, u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (SetSemiring.{u1} α) (instHMul.{u1} (SetSemiring.{u1} α) (NonUnitalNonAssocSemiring.toMul.{u1} (SetSemiring.{u1} α) (SetSemiring.instNonUnitalNonAssocSemiringSetSemiring.{u1} α _inst_1))) x._@.Mathlib.Data.Set.Semiring._hyg.786 x._@.Mathlib.Data.Set.Semiring._hyg.788) (fun (x._@.Mathlib.Data.Set.Semiring._hyg.801 : SetSemiring.{u1} α) (x._@.Mathlib.Data.Set.Semiring._hyg.803 : SetSemiring.{u1} α) => LE.le.{u1} (SetSemiring.{u1} α) (Preorder.toLE.{u1} (SetSemiring.{u1} α) (PartialOrder.toPreorder.{u1} (SetSemiring.{u1} α) (instPartialOrderSetSemiring.{u1} α))) x._@.Mathlib.Data.Set.Semiring._hyg.801 x._@.Mathlib.Data.Set.Semiring._hyg.803)
Case conversion may be inaccurate. Consider using '#align set_semiring.covariant_class_mul_left SetSemiring.covariantClass_mul_leftₓ'. -/
instance covariantClass_mul_left : CovariantClass (SetSemiring α) (SetSemiring α) (· * ·) (· ≤ ·) :=
  ⟨fun a b c => mul_subset_mul_left⟩
#align set_semiring.covariant_class_mul_left SetSemiring.covariantClass_mul_left

/- warning: set_semiring.covariant_class_mul_right -> SetSemiring.covariantClass_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α], CovariantClass.{u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (Function.swap.{succ u1, succ u1, succ u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (fun (ᾰ : SetSemiring.{u1} α) (ᾰ : SetSemiring.{u1} α) => SetSemiring.{u1} α) (HMul.hMul.{u1, u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (SetSemiring.{u1} α) (instHMul.{u1} (SetSemiring.{u1} α) (Distrib.toHasMul.{u1} (SetSemiring.{u1} α) (NonUnitalNonAssocSemiring.toDistrib.{u1} (SetSemiring.{u1} α) (SetSemiring.nonUnitalNonAssocSemiring.{u1} α _inst_1)))))) (LE.le.{u1} (SetSemiring.{u1} α) (Preorder.toHasLe.{u1} (SetSemiring.{u1} α) (PartialOrder.toPreorder.{u1} (SetSemiring.{u1} α) (SetSemiring.partialOrder.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α], CovariantClass.{u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (Function.swap.{succ u1, succ u1, succ u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (fun (ᾰ : SetSemiring.{u1} α) (ᾰ : SetSemiring.{u1} α) => SetSemiring.{u1} α) (fun (x._@.Mathlib.Data.Set.Semiring._hyg.846 : SetSemiring.{u1} α) (x._@.Mathlib.Data.Set.Semiring._hyg.848 : SetSemiring.{u1} α) => HMul.hMul.{u1, u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (SetSemiring.{u1} α) (instHMul.{u1} (SetSemiring.{u1} α) (NonUnitalNonAssocSemiring.toMul.{u1} (SetSemiring.{u1} α) (SetSemiring.instNonUnitalNonAssocSemiringSetSemiring.{u1} α _inst_1))) x._@.Mathlib.Data.Set.Semiring._hyg.846 x._@.Mathlib.Data.Set.Semiring._hyg.848)) (fun (x._@.Mathlib.Data.Set.Semiring._hyg.861 : SetSemiring.{u1} α) (x._@.Mathlib.Data.Set.Semiring._hyg.863 : SetSemiring.{u1} α) => LE.le.{u1} (SetSemiring.{u1} α) (Preorder.toLE.{u1} (SetSemiring.{u1} α) (PartialOrder.toPreorder.{u1} (SetSemiring.{u1} α) (instPartialOrderSetSemiring.{u1} α))) x._@.Mathlib.Data.Set.Semiring._hyg.861 x._@.Mathlib.Data.Set.Semiring._hyg.863)
Case conversion may be inaccurate. Consider using '#align set_semiring.covariant_class_mul_right SetSemiring.covariantClass_mul_rightₓ'. -/
instance covariantClass_mul_right :
    CovariantClass (SetSemiring α) (SetSemiring α) (swap (· * ·)) (· ≤ ·) :=
  ⟨fun a b c => mul_subset_mul_right⟩
#align set_semiring.covariant_class_mul_right SetSemiring.covariantClass_mul_right

end Mul

section One

variable [One α]

instance : One (SetSemiring α) where one := Set.up 1

/- warning: set_semiring.one_def -> SetSemiring.one_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : One.{u1} α], Eq.{succ u1} (SetSemiring.{u1} α) (OfNat.ofNat.{u1} (SetSemiring.{u1} α) 1 (OfNat.mk.{u1} (SetSemiring.{u1} α) 1 (One.one.{u1} (SetSemiring.{u1} α) (SetSemiring.hasOne.{u1} α _inst_1)))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) => (Set.{u1} α) -> (SetSemiring.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.up.{u1} α) (OfNat.ofNat.{u1} (Set.{u1} α) 1 (OfNat.mk.{u1} (Set.{u1} α) 1 (One.one.{u1} (Set.{u1} α) (Set.one.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : One.{u1} α], Eq.{succ u1} (SetSemiring.{u1} α) (OfNat.ofNat.{u1} (SetSemiring.{u1} α) 1 (One.toOfNat1.{u1} (SetSemiring.{u1} α) (SetSemiring.instOneSetSemiring.{u1} α _inst_1))) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.{u1} α) (fun (_x : Set.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Set.{u1} α) => SetSemiring.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.up.{u1} α) (OfNat.ofNat.{u1} (Set.{u1} α) 1 (One.toOfNat1.{u1} (Set.{u1} α) (Set.one.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align set_semiring.one_def SetSemiring.one_defₓ'. -/
theorem one_def : (1 : SetSemiring α) = Set.up 1 :=
  rfl
#align set_semiring.one_def SetSemiring.one_def

#print SetSemiring.down_one /-
@[simp]
theorem down_one : (1 : SetSemiring α).down = 1 :=
  rfl
#align set_semiring.down_one SetSemiring.down_one
-/

#print Set.up_one /-
@[simp]
theorem Set.up_one : (1 : Set α).up = 1 :=
  rfl
#align set.up_one Set.up_one
-/

end One

instance [MulOneClass α] : NonAssocSemiring (SetSemiring α) :=
  { SetSemiring.nonUnitalNonAssocSemiring,
    Set.mulOneClass with
    one := 1
    mul := (· * ·) }

instance [Semigroup α] : NonUnitalSemiring (SetSemiring α) :=
  { SetSemiring.nonUnitalNonAssocSemiring, Set.semigroup with }

instance [Monoid α] : IdemSemiring (SetSemiring α) :=
  { SetSemiring.nonAssocSemiring, SetSemiring.nonUnitalSemiring, Set.completeBooleanAlgebra with }

instance [CommSemigroup α] : NonUnitalCommSemiring (SetSemiring α) :=
  { SetSemiring.nonUnitalSemiring, Set.commSemigroup with }

instance [CommMonoid α] : IdemCommSemiring (SetSemiring α) :=
  { SetSemiring.idemSemiring, Set.commMonoid with }

instance [CommMonoid α] : CanonicallyOrderedCommSemiring (SetSemiring α) :=
  { SetSemiring.idemSemiring, Set.commMonoid,
    SetSemiring.noZeroDivisors with
    add_le_add_left := fun a b => add_le_add_left
    exists_add_of_le := fun a b ab => ⟨b, (union_eq_right_iff_subset.2 ab).symm⟩
    le_self_add := subset_union_left }

/- warning: set_semiring.image_hom -> SetSemiring.imageHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : MulOneClass.{u2} β], (MonoidHom.{u1, u2} α β _inst_1 _inst_2) -> (RingHom.{u1, u2} (SetSemiring.{u1} α) (SetSemiring.{u2} β) (SetSemiring.nonAssocSemiring.{u1} α _inst_1) (SetSemiring.nonAssocSemiring.{u2} β _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : MulOneClass.{u2} β], (MonoidHom.{u1, u2} α β _inst_1 _inst_2) -> (RingHom.{u1, u2} (SetSemiring.{u1} α) (SetSemiring.{u2} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} α _inst_1) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} β _inst_2))
Case conversion may be inaccurate. Consider using '#align set_semiring.image_hom SetSemiring.imageHomₓ'. -/
/-- The image of a set under a multiplicative homomorphism is a ring homomorphism
with respect to the pointwise operations on sets. -/
def imageHom [MulOneClass α] [MulOneClass β] (f : α →* β) : SetSemiring α →+* SetSemiring β
    where
  toFun s := (image f s.down).up
  map_zero' := image_empty _
  map_one' := by rw [down_one, image_one, map_one, singleton_one, Set.up_one]
  map_add' := image_union _
  map_mul' _ _ := image_mul f
#align set_semiring.image_hom SetSemiring.imageHom

/- warning: set_semiring.image_hom_def -> SetSemiring.imageHom_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : MulOneClass.{u2} β] (f : MonoidHom.{u1, u2} α β _inst_1 _inst_2) (s : SetSemiring.{u1} α), Eq.{succ u2} (SetSemiring.{u2} β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} (SetSemiring.{u1} α) (SetSemiring.{u2} β) (SetSemiring.nonAssocSemiring.{u1} α _inst_1) (SetSemiring.nonAssocSemiring.{u2} β _inst_2)) (fun (_x : RingHom.{u1, u2} (SetSemiring.{u1} α) (SetSemiring.{u2} β) (SetSemiring.nonAssocSemiring.{u1} α _inst_1) (SetSemiring.nonAssocSemiring.{u2} β _inst_2)) => (SetSemiring.{u1} α) -> (SetSemiring.{u2} β)) (RingHom.hasCoeToFun.{u1, u2} (SetSemiring.{u1} α) (SetSemiring.{u2} β) (SetSemiring.nonAssocSemiring.{u1} α _inst_1) (SetSemiring.nonAssocSemiring.{u2} β _inst_2)) (SetSemiring.imageHom.{u1, u2} α β _inst_1 _inst_2 f) s) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (Set.{u2} β) (SetSemiring.{u2} β)) (fun (_x : Equiv.{succ u2, succ u2} (Set.{u2} β) (SetSemiring.{u2} β)) => (Set.{u2} β) -> (SetSemiring.{u2} β)) (Equiv.hasCoeToFun.{succ u2, succ u2} (Set.{u2} β) (SetSemiring.{u2} β)) (Set.up.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (MonoidHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) => (SetSemiring.{u1} α) -> (Set.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (SetSemiring.down.{u1} α) s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MulOneClass.{u2} α] [_inst_2 : MulOneClass.{u1} β] (f : MonoidHom.{u2, u1} α β _inst_1 _inst_2) (s : SetSemiring.{u2} α), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : SetSemiring.{u2} α) => SetSemiring.{u1} β) s) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} (SetSemiring.{u2} α) (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2)) (SetSemiring.{u2} α) (fun (_x : SetSemiring.{u2} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : SetSemiring.{u2} α) => SetSemiring.{u1} β) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} (SetSemiring.{u2} α) (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2)) (SetSemiring.{u2} α) (SetSemiring.{u1} β) (NonUnitalNonAssocSemiring.toMul.{u2} (SetSemiring.{u2} α) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} (SetSemiring.{u2} α) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u1} (SetSemiring.{u1} β) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} (SetSemiring.{u2} α) (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2)) (SetSemiring.{u2} α) (SetSemiring.{u1} β) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} (SetSemiring.{u2} α) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} (SetSemiring.{u2} α) (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2)) (SetSemiring.{u2} α) (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2) (RingHom.instRingHomClassRingHom.{u2, u1} (SetSemiring.{u2} α) (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2))))) (SetSemiring.imageHom.{u2, u1} α β _inst_1 _inst_2 f) s) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} β) (SetSemiring.{u1} β)) (Set.{u1} β) (fun (_x : Set.{u1} β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Set.{u1} β) => SetSemiring.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Set.{u1} β) (SetSemiring.{u1} β)) (Set.up.{u1} β) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : α) => β) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β _inst_1 _inst_2) α β (MulOneClass.toMul.{u2} α _inst_1) (MulOneClass.toMul.{u1} β _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} α β _inst_1 _inst_2))) f) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (SetSemiring.{u2} α) (Set.{u2} α)) (SetSemiring.{u2} α) (fun (_x : SetSemiring.{u2} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : SetSemiring.{u2} α) => Set.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} (SetSemiring.{u2} α) (Set.{u2} α)) (SetSemiring.down.{u2} α) s)))
Case conversion may be inaccurate. Consider using '#align set_semiring.image_hom_def SetSemiring.imageHom_defₓ'. -/
theorem imageHom_def [MulOneClass α] [MulOneClass β] (f : α →* β) (s : SetSemiring α) :
    imageHom f s = (image f s.down).up :=
  rfl
#align set_semiring.image_hom_def SetSemiring.imageHom_def

/- warning: set_semiring.down_image_hom -> SetSemiring.down_imageHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : MulOneClass.{u2} β] (f : MonoidHom.{u1, u2} α β _inst_1 _inst_2) (s : SetSemiring.{u1} α), Eq.{succ u2} (Set.{u2} β) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (SetSemiring.{u2} β) (Set.{u2} β)) (fun (_x : Equiv.{succ u2, succ u2} (SetSemiring.{u2} β) (Set.{u2} β)) => (SetSemiring.{u2} β) -> (Set.{u2} β)) (Equiv.hasCoeToFun.{succ u2, succ u2} (SetSemiring.{u2} β) (Set.{u2} β)) (SetSemiring.down.{u2} β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} (SetSemiring.{u1} α) (SetSemiring.{u2} β) (SetSemiring.nonAssocSemiring.{u1} α _inst_1) (SetSemiring.nonAssocSemiring.{u2} β _inst_2)) (fun (_x : RingHom.{u1, u2} (SetSemiring.{u1} α) (SetSemiring.{u2} β) (SetSemiring.nonAssocSemiring.{u1} α _inst_1) (SetSemiring.nonAssocSemiring.{u2} β _inst_2)) => (SetSemiring.{u1} α) -> (SetSemiring.{u2} β)) (RingHom.hasCoeToFun.{u1, u2} (SetSemiring.{u1} α) (SetSemiring.{u2} β) (SetSemiring.nonAssocSemiring.{u1} α _inst_1) (SetSemiring.nonAssocSemiring.{u2} β _inst_2)) (SetSemiring.imageHom.{u1, u2} α β _inst_1 _inst_2 f) s)) (Set.image.{u1, u2} α β (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (MonoidHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) => (SetSemiring.{u1} α) -> (Set.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (SetSemiring.down.{u1} α) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MulOneClass.{u2} α] [_inst_2 : MulOneClass.{u1} β] (f : MonoidHom.{u2, u1} α β _inst_1 _inst_2) (s : SetSemiring.{u2} α), Eq.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : SetSemiring.{u1} β) => Set.{u1} β) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} (SetSemiring.{u2} α) (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2)) (SetSemiring.{u2} α) (fun (a : SetSemiring.{u2} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : SetSemiring.{u2} α) => SetSemiring.{u1} β) a) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} (SetSemiring.{u2} α) (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2)) (SetSemiring.{u2} α) (SetSemiring.{u1} β) (NonUnitalNonAssocSemiring.toMul.{u2} (SetSemiring.{u2} α) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} (SetSemiring.{u2} α) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u1} (SetSemiring.{u1} β) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} (SetSemiring.{u2} α) (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2)) (SetSemiring.{u2} α) (SetSemiring.{u1} β) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} (SetSemiring.{u2} α) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} (SetSemiring.{u2} α) (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2)) (SetSemiring.{u2} α) (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2) (RingHom.instRingHomClassRingHom.{u2, u1} (SetSemiring.{u2} α) (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2))))) (SetSemiring.imageHom.{u2, u1} α β _inst_1 _inst_2 f) s)) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (SetSemiring.{u1} β) (Set.{u1} β)) (SetSemiring.{u1} β) (fun (_x : SetSemiring.{u1} β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : SetSemiring.{u1} β) => Set.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (SetSemiring.{u1} β) (Set.{u1} β)) (SetSemiring.down.{u1} β) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} (SetSemiring.{u2} α) (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2)) (SetSemiring.{u2} α) (fun (_x : SetSemiring.{u2} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : SetSemiring.{u2} α) => SetSemiring.{u1} β) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} (SetSemiring.{u2} α) (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2)) (SetSemiring.{u2} α) (SetSemiring.{u1} β) (NonUnitalNonAssocSemiring.toMul.{u2} (SetSemiring.{u2} α) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} (SetSemiring.{u2} α) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u1} (SetSemiring.{u1} β) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} (SetSemiring.{u2} α) (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2)) (SetSemiring.{u2} α) (SetSemiring.{u1} β) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} (SetSemiring.{u2} α) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} (SetSemiring.{u2} α) (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2)) (SetSemiring.{u2} α) (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2) (RingHom.instRingHomClassRingHom.{u2, u1} (SetSemiring.{u2} α) (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2))))) (SetSemiring.imageHom.{u2, u1} α β _inst_1 _inst_2 f) s)) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : α) => β) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β _inst_1 _inst_2) α β (MulOneClass.toMul.{u2} α _inst_1) (MulOneClass.toMul.{u1} β _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} α β _inst_1 _inst_2))) f) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (SetSemiring.{u2} α) (Set.{u2} α)) (SetSemiring.{u2} α) (fun (_x : SetSemiring.{u2} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : SetSemiring.{u2} α) => Set.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} (SetSemiring.{u2} α) (Set.{u2} α)) (SetSemiring.down.{u2} α) s))
Case conversion may be inaccurate. Consider using '#align set_semiring.down_image_hom SetSemiring.down_imageHomₓ'. -/
@[simp]
theorem down_imageHom [MulOneClass α] [MulOneClass β] (f : α →* β) (s : SetSemiring α) :
    (imageHom f s).down = f '' s.down :=
  rfl
#align set_semiring.down_image_hom SetSemiring.down_imageHom

/- warning: set.up_image -> Set.up_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : MulOneClass.{u2} β] (f : MonoidHom.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u1} α), Eq.{succ u2} (SetSemiring.{u2} β) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (Set.{u2} β) (SetSemiring.{u2} β)) (fun (_x : Equiv.{succ u2, succ u2} (Set.{u2} β) (SetSemiring.{u2} β)) => (Set.{u2} β) -> (SetSemiring.{u2} β)) (Equiv.hasCoeToFun.{succ u2, succ u2} (Set.{u2} β) (SetSemiring.{u2} β)) (Set.up.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (MonoidHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f) s)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} (SetSemiring.{u1} α) (SetSemiring.{u2} β) (SetSemiring.nonAssocSemiring.{u1} α _inst_1) (SetSemiring.nonAssocSemiring.{u2} β _inst_2)) (fun (_x : RingHom.{u1, u2} (SetSemiring.{u1} α) (SetSemiring.{u2} β) (SetSemiring.nonAssocSemiring.{u1} α _inst_1) (SetSemiring.nonAssocSemiring.{u2} β _inst_2)) => (SetSemiring.{u1} α) -> (SetSemiring.{u2} β)) (RingHom.hasCoeToFun.{u1, u2} (SetSemiring.{u1} α) (SetSemiring.{u2} β) (SetSemiring.nonAssocSemiring.{u1} α _inst_1) (SetSemiring.nonAssocSemiring.{u2} β _inst_2)) (SetSemiring.imageHom.{u1, u2} α β _inst_1 _inst_2 f) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) => (Set.{u1} α) -> (SetSemiring.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.up.{u1} α) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MulOneClass.{u2} α] [_inst_2 : MulOneClass.{u1} β] (f : MonoidHom.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u2} α), Eq.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Set.{u1} β) => SetSemiring.{u1} β) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} α β _inst_1 _inst_2) α (fun (a : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : α) => β) a) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β _inst_1 _inst_2) α β (MulOneClass.toMul.{u2} α _inst_1) (MulOneClass.toMul.{u1} β _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} α β _inst_1 _inst_2))) f) s)) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} β) (SetSemiring.{u1} β)) (Set.{u1} β) (fun (_x : Set.{u1} β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Set.{u1} β) => SetSemiring.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Set.{u1} β) (SetSemiring.{u1} β)) (Set.up.{u1} β) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : α) => β) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β _inst_1 _inst_2) α β (MulOneClass.toMul.{u2} α _inst_1) (MulOneClass.toMul.{u1} β _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} α β _inst_1 _inst_2))) f) s)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} (SetSemiring.{u2} α) (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2)) (SetSemiring.{u2} α) (fun (_x : SetSemiring.{u2} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : SetSemiring.{u2} α) => SetSemiring.{u1} β) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} (SetSemiring.{u2} α) (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2)) (SetSemiring.{u2} α) (SetSemiring.{u1} β) (NonUnitalNonAssocSemiring.toMul.{u2} (SetSemiring.{u2} α) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} (SetSemiring.{u2} α) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u1} (SetSemiring.{u1} β) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} (SetSemiring.{u2} α) (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2)) (SetSemiring.{u2} α) (SetSemiring.{u1} β) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} (SetSemiring.{u2} α) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} (SetSemiring.{u2} α) (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2)) (SetSemiring.{u2} α) (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2) (RingHom.instRingHomClassRingHom.{u2, u1} (SetSemiring.{u2} α) (SetSemiring.{u1} β) (SetSemiring.instNonAssocSemiringSetSemiring.{u2} α _inst_1) (SetSemiring.instNonAssocSemiringSetSemiring.{u1} β _inst_2))))) (SetSemiring.imageHom.{u2, u1} α β _inst_1 _inst_2 f) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Set.{u2} α) (SetSemiring.{u2} α)) (Set.{u2} α) (fun (_x : Set.{u2} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Set.{u2} α) => SetSemiring.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} (Set.{u2} α) (SetSemiring.{u2} α)) (Set.up.{u2} α) s))
Case conversion may be inaccurate. Consider using '#align set.up_image Set.up_imageₓ'. -/
@[simp]
theorem Set.up_image [MulOneClass α] [MulOneClass β] (f : α →* β) (s : Set α) :
    (f '' s).up = imageHom f s.up :=
  rfl
#align set.up_image Set.up_image

end SetSemiring

