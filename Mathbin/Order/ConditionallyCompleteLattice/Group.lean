/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module order.conditionally_complete_lattice.group
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.ConditionallyCompleteLattice.Basic
import Mathbin.Algebra.Order.Group.TypeTags

/-!
# Conditionally complete lattices and groups.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/


section Group

variable {α : Type _} {ι : Sort _} {ι' : Sort _} [Nonempty ι] [Nonempty ι']
  [ConditionallyCompleteLattice α] [Group α]

/- warning: le_mul_cinfi -> le_mul_cinfᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Nonempty.{u2} ι] [_inst_3 : ConditionallyCompleteLattice.{u1} α] [_inst_4 : Group.{u1} α] [_inst_5 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_4)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3))))))] {a : α} {g : α} {h : ι -> α}, (forall (j : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3))))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_4))))) g (h j))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3))))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_4))))) g (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_3) ι h)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : Nonempty.{u1} ι] [_inst_3 : ConditionallyCompleteLattice.{u2} α] [_inst_4 : Group.{u2} α] [_inst_5 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.50 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.52 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_4))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.50 x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.52) (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.65 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.67 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_3))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.65 x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.67)] {a : α} {g : α} {h : ι -> α}, (forall (j : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_3))))) a (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_4))))) g (h j))) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_3))))) a (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_4))))) g (infᵢ.{u2, u1} α (ConditionallyCompleteLattice.toInfSet.{u2} α _inst_3) ι h)))
Case conversion may be inaccurate. Consider using '#align le_mul_cinfi le_mul_cinfᵢₓ'. -/
@[to_additive]
theorem le_mul_cinfᵢ [CovariantClass α α (· * ·) (· ≤ ·)] {a : α} {g : α} {h : ι → α}
    (H : ∀ j, a ≤ g * h j) : a ≤ g * infᵢ h :=
  inv_mul_le_iff_le_mul.mp <| le_cinfᵢ fun hi => inv_mul_le_iff_le_mul.mpr <| H _
#align le_mul_cinfi le_mul_cinfᵢ
#align le_add_cinfi le_add_cinfᵢ

/- warning: mul_csupr_le -> mul_csupᵢ_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Nonempty.{u2} ι] [_inst_3 : ConditionallyCompleteLattice.{u1} α] [_inst_4 : Group.{u1} α] [_inst_5 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_4)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3))))))] {a : α} {g : α} {h : ι -> α}, (forall (j : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_4))))) g (h j)) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_4))))) g (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_3) ι h)) a)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : Nonempty.{u1} ι] [_inst_3 : ConditionallyCompleteLattice.{u2} α] [_inst_4 : Group.{u2} α] [_inst_5 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.139 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.141 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_4))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.139 x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.141) (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.154 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.156 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_3))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.154 x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.156)] {a : α} {g : α} {h : ι -> α}, (forall (j : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_3))))) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_4))))) g (h j)) a) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_3))))) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_4))))) g (supᵢ.{u2, u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α _inst_3) ι h)) a)
Case conversion may be inaccurate. Consider using '#align mul_csupr_le mul_csupᵢ_leₓ'. -/
@[to_additive]
theorem mul_csupᵢ_le [CovariantClass α α (· * ·) (· ≤ ·)] {a : α} {g : α} {h : ι → α}
    (H : ∀ j, g * h j ≤ a) : g * supᵢ h ≤ a :=
  @le_mul_cinfᵢ αᵒᵈ _ _ _ _ _ _ _ _ H
#align mul_csupr_le mul_csupᵢ_le
#align add_csupr_le add_csupᵢ_le

/- warning: le_cinfi_mul -> le_cinfᵢ_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Nonempty.{u2} ι] [_inst_3 : ConditionallyCompleteLattice.{u1} α] [_inst_4 : Group.{u1} α] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_4))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3))))))] {a : α} {g : ι -> α} {h : α}, (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3))))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_4))))) (g i) h)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3))))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_4))))) (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_3) ι g) h))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : Nonempty.{u1} ι] [_inst_3 : ConditionallyCompleteLattice.{u2} α] [_inst_4 : Group.{u2} α] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.228 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.230 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_4))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.228 x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.230)) (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.243 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.245 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_3))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.243 x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.245)] {a : α} {g : ι -> α} {h : α}, (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_3))))) a (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_4))))) (g i) h)) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_3))))) a (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_4))))) (infᵢ.{u2, u1} α (ConditionallyCompleteLattice.toInfSet.{u2} α _inst_3) ι g) h))
Case conversion may be inaccurate. Consider using '#align le_cinfi_mul le_cinfᵢ_mulₓ'. -/
@[to_additive]
theorem le_cinfᵢ_mul [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a : α} {g : ι → α}
    {h : α} (H : ∀ i, a ≤ g i * h) : a ≤ infᵢ g * h :=
  mul_inv_le_iff_le_mul.mp <| le_cinfᵢ fun gi => mul_inv_le_iff_le_mul.mpr <| H _
#align le_cinfi_mul le_cinfᵢ_mul
#align le_cinfi_add le_cinfᵢ_add

/- warning: csupr_mul_le -> csupᵢ_mul_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Nonempty.{u2} ι] [_inst_3 : ConditionallyCompleteLattice.{u1} α] [_inst_4 : Group.{u1} α] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_4))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3))))))] {a : α} {g : ι -> α} {h : α}, (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_4))))) (g i) h) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_4))))) (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_3) ι g) h) a)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : Nonempty.{u1} ι] [_inst_3 : ConditionallyCompleteLattice.{u2} α] [_inst_4 : Group.{u2} α] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.320 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.322 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_4))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.320 x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.322)) (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.335 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.337 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_3))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.335 x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.337)] {a : α} {g : ι -> α} {h : α}, (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_3))))) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_4))))) (g i) h) a) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_3))))) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_4))))) (supᵢ.{u2, u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α _inst_3) ι g) h) a)
Case conversion may be inaccurate. Consider using '#align csupr_mul_le csupᵢ_mul_leₓ'. -/
@[to_additive]
theorem csupᵢ_mul_le [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a : α} {g : ι → α}
    {h : α} (H : ∀ i, g i * h ≤ a) : supᵢ g * h ≤ a :=
  @le_cinfᵢ_mul αᵒᵈ _ _ _ _ _ _ _ _ H
#align csupr_mul_le csupᵢ_mul_le
#align csupr_add_le csupᵢ_add_le

/- warning: le_cinfi_mul_cinfi -> le_cinfᵢ_mul_cinfᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : Nonempty.{u2} ι] [_inst_2 : Nonempty.{u3} ι'] [_inst_3 : ConditionallyCompleteLattice.{u1} α] [_inst_4 : Group.{u1} α] [_inst_5 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_4)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3))))))] [_inst_6 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_4))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3))))))] {a : α} {g : ι -> α} {h : ι' -> α}, (forall (i : ι) (j : ι'), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3))))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_4))))) (g i) (h j))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3))))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_4))))) (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_3) ι g) (infᵢ.{u1, u3} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_3) ι' h)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u1}} [_inst_1 : Nonempty.{u2} ι] [_inst_2 : Nonempty.{u1} ι'] [_inst_3 : ConditionallyCompleteLattice.{u3} α] [_inst_4 : Group.{u3} α] [_inst_5 : CovariantClass.{u3, u3} α α (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.406 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.408 : α) => HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_4))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.406 x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.408) (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.421 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.423 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_3))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.421 x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.423)] [_inst_6 : CovariantClass.{u3, u3} α α (Function.swap.{succ u3, succ u3, succ u3} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.443 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.445 : α) => HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_4))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.443 x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.445)) (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.458 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.460 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_3))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.458 x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.460)] {a : α} {g : ι -> α} {h : ι' -> α}, (forall (i : ι) (j : ι'), LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_3))))) a (HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_4))))) (g i) (h j))) -> (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_3))))) a (HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_4))))) (infᵢ.{u3, u2} α (ConditionallyCompleteLattice.toInfSet.{u3} α _inst_3) ι g) (infᵢ.{u3, u1} α (ConditionallyCompleteLattice.toInfSet.{u3} α _inst_3) ι' h)))
Case conversion may be inaccurate. Consider using '#align le_cinfi_mul_cinfi le_cinfᵢ_mul_cinfᵢₓ'. -/
@[to_additive]
theorem le_cinfᵢ_mul_cinfᵢ [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a : α} {g : ι → α} {h : ι' → α}
    (H : ∀ i j, a ≤ g i * h j) : a ≤ infᵢ g * infᵢ h :=
  le_cinfᵢ_mul fun i => le_mul_cinfᵢ <| H _
#align le_cinfi_mul_cinfi le_cinfᵢ_mul_cinfᵢ
#align le_cinfi_add_cinfi le_cinfᵢ_add_cinfᵢ

/- warning: csupr_mul_csupr_le -> csupᵢ_mul_csupᵢ_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : Nonempty.{u2} ι] [_inst_2 : Nonempty.{u3} ι'] [_inst_3 : ConditionallyCompleteLattice.{u1} α] [_inst_4 : Group.{u1} α] [_inst_5 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_4)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3))))))] [_inst_6 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_4))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3))))))] {a : α} {g : ι -> α} {h : ι' -> α}, (forall (i : ι) (j : ι'), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_4))))) (g i) (h j)) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_3))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_4))))) (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_3) ι g) (supᵢ.{u1, u3} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_3) ι' h)) a)
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u1}} [_inst_1 : Nonempty.{u2} ι] [_inst_2 : Nonempty.{u1} ι'] [_inst_3 : ConditionallyCompleteLattice.{u3} α] [_inst_4 : Group.{u3} α] [_inst_5 : CovariantClass.{u3, u3} α α (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.534 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.536 : α) => HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_4))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.534 x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.536) (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.549 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.551 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_3))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.549 x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.551)] [_inst_6 : CovariantClass.{u3, u3} α α (Function.swap.{succ u3, succ u3, succ u3} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.571 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.573 : α) => HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_4))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.571 x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.573)) (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.586 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.588 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_3))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.586 x._@.Mathlib.Order.ConditionallyCompleteLattice.Group._hyg.588)] {a : α} {g : ι -> α} {h : ι' -> α}, (forall (i : ι) (j : ι'), LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_3))))) (HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_4))))) (g i) (h j)) a) -> (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_3))))) (HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_4))))) (supᵢ.{u3, u2} α (ConditionallyCompleteLattice.toSupSet.{u3} α _inst_3) ι g) (supᵢ.{u3, u1} α (ConditionallyCompleteLattice.toSupSet.{u3} α _inst_3) ι' h)) a)
Case conversion may be inaccurate. Consider using '#align csupr_mul_csupr_le csupᵢ_mul_csupᵢ_leₓ'. -/
@[to_additive]
theorem csupᵢ_mul_csupᵢ_le [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a : α} {g : ι → α} {h : ι' → α}
    (H : ∀ i j, g i * h j ≤ a) : supᵢ g * supᵢ h ≤ a :=
  csupᵢ_mul_le fun i => mul_csupᵢ_le <| H _
#align csupr_mul_csupr_le csupᵢ_mul_csupᵢ_le
#align csupr_add_csupr_le csupᵢ_add_csupᵢ_le

end Group

