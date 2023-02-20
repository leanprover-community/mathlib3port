/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module data.set.semiring
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
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
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (LE.le.{u1} (SetSemiring.{u1} α) (Preorder.toLE.{u1} (SetSemiring.{u1} α) (PartialOrder.toPreorder.{u1} (SetSemiring.{u1} α) (SetSemiring.partialOrder.{u1} α))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) => (Set.{u1} α) -> (SetSemiring.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.up.{u1} α) s) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) => (Set.{u1} α) -> (SetSemiring.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.up.{u1} α) t)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (LE.le.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Set.{u1} α) => SetSemiring.{u1} α) s) (Preorder.toLE.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Set.{u1} α) => SetSemiring.{u1} α) s) (PartialOrder.toPreorder.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Set.{u1} α) => SetSemiring.{u1} α) s) (instPartialOrderSetSemiring.{u1} α))) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.{u1} α) (fun (_x : Set.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Set.{u1} α) => SetSemiring.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.up.{u1} α) s) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.{u1} α) (fun (_x : Set.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Set.{u1} α) => SetSemiring.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.up.{u1} α) t)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set_semiring.up_le_up SetSemiring.up_le_upₓ'. -/
-- TODO: These lemmas are not tagged `simp` because `set.le_eq_subset` simplifies the LHS
theorem up_le_up {s t : Set α} : s.up ≤ t.up ↔ s ⊆ t :=
  Iff.rfl
#align set_semiring.up_le_up SetSemiring.up_le_up

/- warning: set_semiring.up_lt_up -> SetSemiring.up_lt_up is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (LT.lt.{u1} (SetSemiring.{u1} α) (Preorder.toLT.{u1} (SetSemiring.{u1} α) (PartialOrder.toPreorder.{u1} (SetSemiring.{u1} α) (SetSemiring.partialOrder.{u1} α))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) => (Set.{u1} α) -> (SetSemiring.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.up.{u1} α) s) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) => (Set.{u1} α) -> (SetSemiring.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.up.{u1} α) t)) (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (LT.lt.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Set.{u1} α) => SetSemiring.{u1} α) s) (Preorder.toLT.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Set.{u1} α) => SetSemiring.{u1} α) s) (PartialOrder.toPreorder.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Set.{u1} α) => SetSemiring.{u1} α) s) (instPartialOrderSetSemiring.{u1} α))) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.{u1} α) (fun (_x : Set.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Set.{u1} α) => SetSemiring.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.up.{u1} α) s) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.{u1} α) (fun (_x : Set.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Set.{u1} α) => SetSemiring.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Set.{u1} α) (SetSemiring.{u1} α)) (Set.up.{u1} α) t)) (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s t)
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
  forall {α : Type.{u1}} {s : SetSemiring.{u1} α} {t : SetSemiring.{u1} α}, Iff (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) => (SetSemiring.{u1} α) -> (Set.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (SetSemiring.down.{u1} α) s) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) => (SetSemiring.{u1} α) -> (Set.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (SetSemiring.down.{u1} α) t)) (LT.lt.{u1} (SetSemiring.{u1} α) (Preorder.toLT.{u1} (SetSemiring.{u1} α) (PartialOrder.toPreorder.{u1} (SetSemiring.{u1} α) (SetSemiring.partialOrder.{u1} α))) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : SetSemiring.{u1} α} {t : SetSemiring.{u1} α}, Iff (HasSSubset.SSubset.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : SetSemiring.{u1} α) => Set.{u1} α) s) (Set.instHasSSubsetSet.{u1} α) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (SetSemiring.{u1} α) (fun (_x : SetSemiring.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : SetSemiring.{u1} α) => Set.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (SetSemiring.down.{u1} α) s) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (SetSemiring.{u1} α) (fun (_x : SetSemiring.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : SetSemiring.{u1} α) => Set.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (SetSemiring.{u1} α) (Set.{u1} α)) (SetSemiring.down.{u1} α) t)) (LT.lt.{u1} (SetSemiring.{u1} α) (Preorder.toLT.{u1} (SetSemiring.{u1} α) (PartialOrder.toPreorder.{u1} (SetSemiring.{u1} α) (instPartialOrderSetSemiring.{u1} α))) s t)
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

/- warning: set_semiring.covariant_class_add -> SetSemiring.covariantClass_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, CovariantClass.{u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (HAdd.hAdd.{u1, u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (SetSemiring.{u1} α) (instHAdd.{u1} (SetSemiring.{u1} α) (AddZeroClass.toHasAdd.{u1} (SetSemiring.{u1} α) (AddMonoid.toAddZeroClass.{u1} (SetSemiring.{u1} α) (AddCommMonoid.toAddMonoid.{u1} (SetSemiring.{u1} α) (SetSemiring.addCommMonoid.{u1} α)))))) (LE.le.{u1} (SetSemiring.{u1} α) (Preorder.toLE.{u1} (SetSemiring.{u1} α) (PartialOrder.toPreorder.{u1} (SetSemiring.{u1} α) (SetSemiring.partialOrder.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}}, CovariantClass.{u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (fun (x._@.Mathlib.Data.Set.Semiring._hyg.341 : SetSemiring.{u1} α) (x._@.Mathlib.Data.Set.Semiring._hyg.343 : SetSemiring.{u1} α) => HAdd.hAdd.{u1, u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (SetSemiring.{u1} α) (instHAdd.{u1} (SetSemiring.{u1} α) (AddZeroClass.toAdd.{u1} (SetSemiring.{u1} α) (AddMonoid.toAddZeroClass.{u1} (SetSemiring.{u1} α) (AddCommMonoid.toAddMonoid.{u1} (SetSemiring.{u1} α) (SetSemiring.instAddCommMonoidSetSemiring.{u1} α))))) x._@.Mathlib.Data.Set.Semiring._hyg.341 x._@.Mathlib.Data.Set.Semiring._hyg.343) (fun (x._@.Mathlib.Data.Set.Semiring._hyg.356 : SetSemiring.{u1} α) (x._@.Mathlib.Data.Set.Semiring._hyg.358 : SetSemiring.{u1} α) => LE.le.{u1} (SetSemiring.{u1} α) (Preorder.toLE.{u1} (SetSemiring.{u1} α) (PartialOrder.toPreorder.{u1} (SetSemiring.{u1} α) (instPartialOrderSetSemiring.{u1} α))) x._@.Mathlib.Data.Set.Semiring._hyg.356 x._@.Mathlib.Data.Set.Semiring._hyg.358)
Case conversion may be inaccurate. Consider using '#align set_semiring.covariant_class_add SetSemiring.covariantClass_addₓ'. -/
/- Since addition on `set_semiring` is commutative (it is set union), there is no need
to also have the instance `covariant_class (set_semiring α) (set_semiring α) (swap (+)) (≤)`. -/
instance covariantClass_add : CovariantClass (SetSemiring α) (SetSemiring α) (· + ·) (· ≤ ·) :=
  ⟨fun a b c => union_subset_union_right _⟩
#align set_semiring.covariant_class_add SetSemiring.covariantClass_add

section Mul

variable [Mul α]

instance : NonUnitalNonAssocSemiring (SetSemiring α) :=
  {
    SetSemiring.addCommMonoid with
    mul := fun s t => (image2 (· * ·) s.down t.down).up
    zero_mul := fun s => empty_mul
    mul_zero := fun s => mul_empty
    left_distrib := fun _ _ _ => mul_union
    right_distrib := fun _ _ _ => union_mul }

instance : NoZeroDivisors (SetSemiring α) :=
  ⟨fun a b ab =>
    a.eq_empty_or_nonempty.imp_right fun ha =>
      b.eq_empty_or_nonempty.resolve_right fun hb =>
        Nonempty.ne_empty ⟨_, mul_mem_mul ha.some_mem hb.some_mem⟩ ab⟩

/- warning: set_semiring.covariant_class_mul_left -> SetSemiring.covariantClass_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α], CovariantClass.{u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (HMul.hMul.{u1, u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (SetSemiring.{u1} α) (instHMul.{u1} (SetSemiring.{u1} α) (Distrib.toHasMul.{u1} (SetSemiring.{u1} α) (NonUnitalNonAssocSemiring.toDistrib.{u1} (SetSemiring.{u1} α) (SetSemiring.nonUnitalNonAssocSemiring.{u1} α _inst_1))))) (LE.le.{u1} (SetSemiring.{u1} α) (Preorder.toLE.{u1} (SetSemiring.{u1} α) (PartialOrder.toPreorder.{u1} (SetSemiring.{u1} α) (SetSemiring.partialOrder.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α], CovariantClass.{u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (fun (x._@.Mathlib.Data.Set.Semiring._hyg.533 : SetSemiring.{u1} α) (x._@.Mathlib.Data.Set.Semiring._hyg.535 : SetSemiring.{u1} α) => HMul.hMul.{u1, u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (SetSemiring.{u1} α) (instHMul.{u1} (SetSemiring.{u1} α) (NonUnitalNonAssocSemiring.toMul.{u1} (SetSemiring.{u1} α) (SetSemiring.instNonUnitalNonAssocSemiringSetSemiring.{u1} α _inst_1))) x._@.Mathlib.Data.Set.Semiring._hyg.533 x._@.Mathlib.Data.Set.Semiring._hyg.535) (fun (x._@.Mathlib.Data.Set.Semiring._hyg.548 : SetSemiring.{u1} α) (x._@.Mathlib.Data.Set.Semiring._hyg.550 : SetSemiring.{u1} α) => LE.le.{u1} (SetSemiring.{u1} α) (Preorder.toLE.{u1} (SetSemiring.{u1} α) (PartialOrder.toPreorder.{u1} (SetSemiring.{u1} α) (instPartialOrderSetSemiring.{u1} α))) x._@.Mathlib.Data.Set.Semiring._hyg.548 x._@.Mathlib.Data.Set.Semiring._hyg.550)
Case conversion may be inaccurate. Consider using '#align set_semiring.covariant_class_mul_left SetSemiring.covariantClass_mul_leftₓ'. -/
instance covariantClass_mul_left : CovariantClass (SetSemiring α) (SetSemiring α) (· * ·) (· ≤ ·) :=
  ⟨fun a b c => mul_subset_mul_left⟩
#align set_semiring.covariant_class_mul_left SetSemiring.covariantClass_mul_left

/- warning: set_semiring.covariant_class_mul_right -> SetSemiring.covariantClass_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α], CovariantClass.{u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (Function.swap.{succ u1, succ u1, succ u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (fun (ᾰ : SetSemiring.{u1} α) (ᾰ : SetSemiring.{u1} α) => SetSemiring.{u1} α) (HMul.hMul.{u1, u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (SetSemiring.{u1} α) (instHMul.{u1} (SetSemiring.{u1} α) (Distrib.toHasMul.{u1} (SetSemiring.{u1} α) (NonUnitalNonAssocSemiring.toDistrib.{u1} (SetSemiring.{u1} α) (SetSemiring.nonUnitalNonAssocSemiring.{u1} α _inst_1)))))) (LE.le.{u1} (SetSemiring.{u1} α) (Preorder.toLE.{u1} (SetSemiring.{u1} α) (PartialOrder.toPreorder.{u1} (SetSemiring.{u1} α) (SetSemiring.partialOrder.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α], CovariantClass.{u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (Function.swap.{succ u1, succ u1, succ u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (fun (ᾰ : SetSemiring.{u1} α) (ᾰ : SetSemiring.{u1} α) => SetSemiring.{u1} α) (fun (x._@.Mathlib.Data.Set.Semiring._hyg.593 : SetSemiring.{u1} α) (x._@.Mathlib.Data.Set.Semiring._hyg.595 : SetSemiring.{u1} α) => HMul.hMul.{u1, u1, u1} (SetSemiring.{u1} α) (SetSemiring.{u1} α) (SetSemiring.{u1} α) (instHMul.{u1} (SetSemiring.{u1} α) (NonUnitalNonAssocSemiring.toMul.{u1} (SetSemiring.{u1} α) (SetSemiring.instNonUnitalNonAssocSemiringSetSemiring.{u1} α _inst_1))) x._@.Mathlib.Data.Set.Semiring._hyg.593 x._@.Mathlib.Data.Set.Semiring._hyg.595)) (fun (x._@.Mathlib.Data.Set.Semiring._hyg.608 : SetSemiring.{u1} α) (x._@.Mathlib.Data.Set.Semiring._hyg.610 : SetSemiring.{u1} α) => LE.le.{u1} (SetSemiring.{u1} α) (Preorder.toLE.{u1} (SetSemiring.{u1} α) (PartialOrder.toPreorder.{u1} (SetSemiring.{u1} α) (instPartialOrderSetSemiring.{u1} α))) x._@.Mathlib.Data.Set.Semiring._hyg.608 x._@.Mathlib.Data.Set.Semiring._hyg.610)
Case conversion may be inaccurate. Consider using '#align set_semiring.covariant_class_mul_right SetSemiring.covariantClass_mul_rightₓ'. -/
instance covariantClass_mul_right :
    CovariantClass (SetSemiring α) (SetSemiring α) (swap (· * ·)) (· ≤ ·) :=
  ⟨fun a b c => mul_subset_mul_right⟩
#align set_semiring.covariant_class_mul_right SetSemiring.covariantClass_mul_right

end Mul

instance [MulOneClass α] : NonAssocSemiring (SetSemiring α) :=
  { SetSemiring.nonUnitalNonAssocSemiring,
    Set.mulOneClass with
    one := 1
    mul := (· * ·) }

instance [Semigroup α] : NonUnitalSemiring (SetSemiring α) :=
  { SetSemiring.nonUnitalNonAssocSemiring, Set.semigroup with }

instance [Monoid α] : Semiring (SetSemiring α) :=
  { SetSemiring.nonAssocSemiring, SetSemiring.nonUnitalSemiring with }

instance [CommSemigroup α] : NonUnitalCommSemiring (SetSemiring α) :=
  { SetSemiring.nonUnitalSemiring, Set.commSemigroup with }

instance [CommMonoid α] : CanonicallyOrderedCommSemiring (SetSemiring α) :=
  { SetSemiring.semiring, Set.commMonoid, SetSemiring.partialOrder _, SetSemiring.orderBot _,
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
  toFun := image f
  map_zero' := image_empty _
  map_one' := by rw [image_one, map_one, singleton_one]
  map_add' := image_union _
  map_mul' _ _ := image_mul f
#align set_semiring.image_hom SetSemiring.imageHom

end SetSemiring

