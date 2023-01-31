/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module algebra.bounds
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Group.OrderIso
import Mathbin.Algebra.Order.Monoid.OrderDual
import Mathbin.Data.Set.Pointwise.Basic
import Mathbin.Order.Bounds.OrderIso
import Mathbin.Order.ConditionallyCompleteLattice.Basic

/-!
# Upper/lower bounds in ordered monoids and groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove a few facts like “`-s` is bounded above iff `s` is bounded below”
(`bdd_above_neg`).
-/


open Function Set

open Pointwise

section inv_neg

variable {G : Type _} [Group G] [Preorder G] [CovariantClass G G (· * ·) (· ≤ ·)]
  [CovariantClass G G (swap (· * ·)) (· ≤ ·)] {s : Set G} {a : G}

/- warning: bdd_above_inv -> bddAbove_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] {s : Set.{u1} G}, Iff (BddAbove.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) s)) (BddBelow.{u1} G _inst_2 s)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (fun (x._@.Mathlib.Algebra.Bounds._hyg.110 : G) (x._@.Mathlib.Algebra.Bounds._hyg.112 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.110 x._@.Mathlib.Algebra.Bounds._hyg.112) (fun (x._@.Mathlib.Algebra.Bounds._hyg.125 : G) (x._@.Mathlib.Algebra.Bounds._hyg.127 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.125 x._@.Mathlib.Algebra.Bounds._hyg.127)] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (fun (x._@.Mathlib.Algebra.Bounds._hyg.147 : G) (x._@.Mathlib.Algebra.Bounds._hyg.149 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.147 x._@.Mathlib.Algebra.Bounds._hyg.149)) (fun (x._@.Mathlib.Algebra.Bounds._hyg.162 : G) (x._@.Mathlib.Algebra.Bounds._hyg.164 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.162 x._@.Mathlib.Algebra.Bounds._hyg.164)] {s : Set.{u1} G}, Iff (BddAbove.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))) s)) (BddBelow.{u1} G _inst_2 s)
Case conversion may be inaccurate. Consider using '#align bdd_above_inv bddAbove_invₓ'. -/
@[simp, to_additive]
theorem bddAbove_inv : BddAbove s⁻¹ ↔ BddBelow s :=
  (OrderIso.inv G).bdd_above_preimage
#align bdd_above_inv bddAbove_inv
#align bdd_above_neg bddAbove_neg

/- warning: bdd_below_inv -> bddBelow_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] {s : Set.{u1} G}, Iff (BddBelow.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) s)) (BddAbove.{u1} G _inst_2 s)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (fun (x._@.Mathlib.Algebra.Bounds._hyg.209 : G) (x._@.Mathlib.Algebra.Bounds._hyg.211 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.209 x._@.Mathlib.Algebra.Bounds._hyg.211) (fun (x._@.Mathlib.Algebra.Bounds._hyg.224 : G) (x._@.Mathlib.Algebra.Bounds._hyg.226 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.224 x._@.Mathlib.Algebra.Bounds._hyg.226)] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (fun (x._@.Mathlib.Algebra.Bounds._hyg.246 : G) (x._@.Mathlib.Algebra.Bounds._hyg.248 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.246 x._@.Mathlib.Algebra.Bounds._hyg.248)) (fun (x._@.Mathlib.Algebra.Bounds._hyg.261 : G) (x._@.Mathlib.Algebra.Bounds._hyg.263 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.261 x._@.Mathlib.Algebra.Bounds._hyg.263)] {s : Set.{u1} G}, Iff (BddBelow.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))) s)) (BddAbove.{u1} G _inst_2 s)
Case conversion may be inaccurate. Consider using '#align bdd_below_inv bddBelow_invₓ'. -/
@[simp, to_additive]
theorem bddBelow_inv : BddBelow s⁻¹ ↔ BddAbove s :=
  (OrderIso.inv G).bdd_below_preimage
#align bdd_below_inv bddBelow_inv
#align bdd_below_neg bddBelow_neg

/- warning: bdd_above.inv -> BddAbove.inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] {s : Set.{u1} G}, (BddAbove.{u1} G _inst_2 s) -> (BddBelow.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) s))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (fun (x._@.Mathlib.Algebra.Bounds._hyg.311 : G) (x._@.Mathlib.Algebra.Bounds._hyg.313 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.311 x._@.Mathlib.Algebra.Bounds._hyg.313) (fun (x._@.Mathlib.Algebra.Bounds._hyg.326 : G) (x._@.Mathlib.Algebra.Bounds._hyg.328 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.326 x._@.Mathlib.Algebra.Bounds._hyg.328)] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (fun (x._@.Mathlib.Algebra.Bounds._hyg.348 : G) (x._@.Mathlib.Algebra.Bounds._hyg.350 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.348 x._@.Mathlib.Algebra.Bounds._hyg.350)) (fun (x._@.Mathlib.Algebra.Bounds._hyg.363 : G) (x._@.Mathlib.Algebra.Bounds._hyg.365 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.363 x._@.Mathlib.Algebra.Bounds._hyg.365)] {s : Set.{u1} G}, (BddAbove.{u1} G _inst_2 s) -> (BddBelow.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))) s))
Case conversion may be inaccurate. Consider using '#align bdd_above.inv BddAbove.invₓ'. -/
@[to_additive]
theorem BddAbove.inv (h : BddAbove s) : BddBelow s⁻¹ :=
  bddBelow_inv.2 h
#align bdd_above.inv BddAbove.inv
#align bdd_above.neg BddAbove.neg

/- warning: bdd_below.inv -> BddBelow.inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] {s : Set.{u1} G}, (BddBelow.{u1} G _inst_2 s) -> (BddAbove.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) s))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (fun (x._@.Mathlib.Algebra.Bounds._hyg.408 : G) (x._@.Mathlib.Algebra.Bounds._hyg.410 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.408 x._@.Mathlib.Algebra.Bounds._hyg.410) (fun (x._@.Mathlib.Algebra.Bounds._hyg.423 : G) (x._@.Mathlib.Algebra.Bounds._hyg.425 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.423 x._@.Mathlib.Algebra.Bounds._hyg.425)] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (fun (x._@.Mathlib.Algebra.Bounds._hyg.445 : G) (x._@.Mathlib.Algebra.Bounds._hyg.447 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.445 x._@.Mathlib.Algebra.Bounds._hyg.447)) (fun (x._@.Mathlib.Algebra.Bounds._hyg.460 : G) (x._@.Mathlib.Algebra.Bounds._hyg.462 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.460 x._@.Mathlib.Algebra.Bounds._hyg.462)] {s : Set.{u1} G}, (BddBelow.{u1} G _inst_2 s) -> (BddAbove.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))) s))
Case conversion may be inaccurate. Consider using '#align bdd_below.inv BddBelow.invₓ'. -/
@[to_additive]
theorem BddBelow.inv (h : BddBelow s) : BddAbove s⁻¹ :=
  bddAbove_inv.2 h
#align bdd_below.inv BddBelow.inv
#align bdd_below.neg BddBelow.neg

/- warning: is_lub_inv -> isLUB_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] {s : Set.{u1} G} {a : G}, Iff (IsLUB.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) s) a) (IsGLB.{u1} G _inst_2 s (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (fun (x._@.Mathlib.Algebra.Bounds._hyg.502 : G) (x._@.Mathlib.Algebra.Bounds._hyg.504 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.502 x._@.Mathlib.Algebra.Bounds._hyg.504) (fun (x._@.Mathlib.Algebra.Bounds._hyg.517 : G) (x._@.Mathlib.Algebra.Bounds._hyg.519 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.517 x._@.Mathlib.Algebra.Bounds._hyg.519)] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (fun (x._@.Mathlib.Algebra.Bounds._hyg.539 : G) (x._@.Mathlib.Algebra.Bounds._hyg.541 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.539 x._@.Mathlib.Algebra.Bounds._hyg.541)) (fun (x._@.Mathlib.Algebra.Bounds._hyg.554 : G) (x._@.Mathlib.Algebra.Bounds._hyg.556 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.554 x._@.Mathlib.Algebra.Bounds._hyg.556)] {s : Set.{u1} G} {a : G}, Iff (IsLUB.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))) s) a) (IsGLB.{u1} G _inst_2 s (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align is_lub_inv isLUB_invₓ'. -/
@[simp, to_additive]
theorem isLUB_inv : IsLUB s⁻¹ a ↔ IsGLB s a⁻¹ :=
  (OrderIso.inv G).is_lub_preimage
#align is_lub_inv isLUB_inv
#align is_lub_neg isLUB_neg

/- warning: is_lub_inv' -> isLUB_inv' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] {s : Set.{u1} G} {a : G}, Iff (IsLUB.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) s) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a)) (IsGLB.{u1} G _inst_2 s a)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (fun (x._@.Mathlib.Algebra.Bounds._hyg.606 : G) (x._@.Mathlib.Algebra.Bounds._hyg.608 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.606 x._@.Mathlib.Algebra.Bounds._hyg.608) (fun (x._@.Mathlib.Algebra.Bounds._hyg.621 : G) (x._@.Mathlib.Algebra.Bounds._hyg.623 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.621 x._@.Mathlib.Algebra.Bounds._hyg.623)] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (fun (x._@.Mathlib.Algebra.Bounds._hyg.643 : G) (x._@.Mathlib.Algebra.Bounds._hyg.645 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.643 x._@.Mathlib.Algebra.Bounds._hyg.645)) (fun (x._@.Mathlib.Algebra.Bounds._hyg.658 : G) (x._@.Mathlib.Algebra.Bounds._hyg.660 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.658 x._@.Mathlib.Algebra.Bounds._hyg.660)] {s : Set.{u1} G} {a : G}, Iff (IsLUB.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))) s) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a)) (IsGLB.{u1} G _inst_2 s a)
Case conversion may be inaccurate. Consider using '#align is_lub_inv' isLUB_inv'ₓ'. -/
@[to_additive]
theorem isLUB_inv' : IsLUB s⁻¹ a⁻¹ ↔ IsGLB s a :=
  (OrderIso.inv G).is_lub_preimage'
#align is_lub_inv' isLUB_inv'
#align is_lub_neg' isLUB_neg'

/- warning: is_glb.inv -> IsGLB.inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] {s : Set.{u1} G} {a : G}, (IsGLB.{u1} G _inst_2 s a) -> (IsLUB.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) s) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (fun (x._@.Mathlib.Algebra.Bounds._hyg.713 : G) (x._@.Mathlib.Algebra.Bounds._hyg.715 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.713 x._@.Mathlib.Algebra.Bounds._hyg.715) (fun (x._@.Mathlib.Algebra.Bounds._hyg.728 : G) (x._@.Mathlib.Algebra.Bounds._hyg.730 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.728 x._@.Mathlib.Algebra.Bounds._hyg.730)] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (fun (x._@.Mathlib.Algebra.Bounds._hyg.750 : G) (x._@.Mathlib.Algebra.Bounds._hyg.752 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.750 x._@.Mathlib.Algebra.Bounds._hyg.752)) (fun (x._@.Mathlib.Algebra.Bounds._hyg.765 : G) (x._@.Mathlib.Algebra.Bounds._hyg.767 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.765 x._@.Mathlib.Algebra.Bounds._hyg.767)] {s : Set.{u1} G} {a : G}, (IsGLB.{u1} G _inst_2 s a) -> (IsLUB.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))) s) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align is_glb.inv IsGLB.invₓ'. -/
@[to_additive]
theorem IsGLB.inv (h : IsGLB s a) : IsLUB s⁻¹ a⁻¹ :=
  isLUB_inv'.2 h
#align is_glb.inv IsGLB.inv
#align is_glb.neg IsGLB.neg

/- warning: is_glb_inv -> isGLB_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] {s : Set.{u1} G} {a : G}, Iff (IsGLB.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) s) a) (IsLUB.{u1} G _inst_2 s (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (fun (x._@.Mathlib.Algebra.Bounds._hyg.812 : G) (x._@.Mathlib.Algebra.Bounds._hyg.814 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.812 x._@.Mathlib.Algebra.Bounds._hyg.814) (fun (x._@.Mathlib.Algebra.Bounds._hyg.827 : G) (x._@.Mathlib.Algebra.Bounds._hyg.829 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.827 x._@.Mathlib.Algebra.Bounds._hyg.829)] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (fun (x._@.Mathlib.Algebra.Bounds._hyg.849 : G) (x._@.Mathlib.Algebra.Bounds._hyg.851 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.849 x._@.Mathlib.Algebra.Bounds._hyg.851)) (fun (x._@.Mathlib.Algebra.Bounds._hyg.864 : G) (x._@.Mathlib.Algebra.Bounds._hyg.866 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.864 x._@.Mathlib.Algebra.Bounds._hyg.866)] {s : Set.{u1} G} {a : G}, Iff (IsGLB.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))) s) a) (IsLUB.{u1} G _inst_2 s (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align is_glb_inv isGLB_invₓ'. -/
@[simp, to_additive]
theorem isGLB_inv : IsGLB s⁻¹ a ↔ IsLUB s a⁻¹ :=
  (OrderIso.inv G).is_glb_preimage
#align is_glb_inv isGLB_inv
#align is_glb_neg isGLB_neg

/- warning: is_glb_inv' -> isGLB_inv' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] {s : Set.{u1} G} {a : G}, Iff (IsGLB.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) s) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a)) (IsLUB.{u1} G _inst_2 s a)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (fun (x._@.Mathlib.Algebra.Bounds._hyg.916 : G) (x._@.Mathlib.Algebra.Bounds._hyg.918 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.916 x._@.Mathlib.Algebra.Bounds._hyg.918) (fun (x._@.Mathlib.Algebra.Bounds._hyg.931 : G) (x._@.Mathlib.Algebra.Bounds._hyg.933 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.931 x._@.Mathlib.Algebra.Bounds._hyg.933)] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (fun (x._@.Mathlib.Algebra.Bounds._hyg.953 : G) (x._@.Mathlib.Algebra.Bounds._hyg.955 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.953 x._@.Mathlib.Algebra.Bounds._hyg.955)) (fun (x._@.Mathlib.Algebra.Bounds._hyg.968 : G) (x._@.Mathlib.Algebra.Bounds._hyg.970 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.968 x._@.Mathlib.Algebra.Bounds._hyg.970)] {s : Set.{u1} G} {a : G}, Iff (IsGLB.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))) s) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a)) (IsLUB.{u1} G _inst_2 s a)
Case conversion may be inaccurate. Consider using '#align is_glb_inv' isGLB_inv'ₓ'. -/
@[to_additive]
theorem isGLB_inv' : IsGLB s⁻¹ a⁻¹ ↔ IsLUB s a :=
  (OrderIso.inv G).is_glb_preimage'
#align is_glb_inv' isGLB_inv'
#align is_glb_neg' isGLB_neg'

/- warning: is_lub.inv -> IsLUB.inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] {s : Set.{u1} G} {a : G}, (IsLUB.{u1} G _inst_2 s a) -> (IsGLB.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) s) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (fun (x._@.Mathlib.Algebra.Bounds._hyg.1023 : G) (x._@.Mathlib.Algebra.Bounds._hyg.1025 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.1023 x._@.Mathlib.Algebra.Bounds._hyg.1025) (fun (x._@.Mathlib.Algebra.Bounds._hyg.1038 : G) (x._@.Mathlib.Algebra.Bounds._hyg.1040 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.1038 x._@.Mathlib.Algebra.Bounds._hyg.1040)] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (fun (x._@.Mathlib.Algebra.Bounds._hyg.1060 : G) (x._@.Mathlib.Algebra.Bounds._hyg.1062 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.1060 x._@.Mathlib.Algebra.Bounds._hyg.1062)) (fun (x._@.Mathlib.Algebra.Bounds._hyg.1075 : G) (x._@.Mathlib.Algebra.Bounds._hyg.1077 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.1075 x._@.Mathlib.Algebra.Bounds._hyg.1077)] {s : Set.{u1} G} {a : G}, (IsLUB.{u1} G _inst_2 s a) -> (IsGLB.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))) s) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align is_lub.inv IsLUB.invₓ'. -/
@[to_additive]
theorem IsLUB.inv (h : IsLUB s a) : IsGLB s⁻¹ a⁻¹ :=
  isGLB_inv'.2 h
#align is_lub.inv IsLUB.inv
#align is_lub.neg IsLUB.neg

end inv_neg

section mul_add

variable {M : Type _} [Mul M] [Preorder M] [CovariantClass M M (· * ·) (· ≤ ·)]
  [CovariantClass M M (swap (· * ·)) (· ≤ ·)]

#print mul_mem_upperBounds_mul /-
@[to_additive]
theorem mul_mem_upperBounds_mul {s t : Set M} {a b : M} (ha : a ∈ upperBounds s)
    (hb : b ∈ upperBounds t) : a * b ∈ upperBounds (s * t) :=
  forall_image2_iff.2 fun x hx y hy => mul_le_mul' (ha hx) (hb hy)
#align mul_mem_upper_bounds_mul mul_mem_upperBounds_mul
#align add_mem_upper_bounds_add add_mem_upperBounds_add
-/

#print subset_upperBounds_mul /-
@[to_additive]
theorem subset_upperBounds_mul (s t : Set M) :
    upperBounds s * upperBounds t ⊆ upperBounds (s * t) :=
  image2_subset_iff.2 fun x hx y hy => mul_mem_upperBounds_mul hx hy
#align subset_upper_bounds_mul subset_upperBounds_mul
#align subset_upper_bounds_add subset_upperBounds_add
-/

#print mul_mem_lowerBounds_mul /-
@[to_additive]
theorem mul_mem_lowerBounds_mul {s t : Set M} {a b : M} (ha : a ∈ lowerBounds s)
    (hb : b ∈ lowerBounds t) : a * b ∈ lowerBounds (s * t) :=
  @mul_mem_upperBounds_mul Mᵒᵈ _ _ _ _ _ _ _ _ ha hb
#align mul_mem_lower_bounds_mul mul_mem_lowerBounds_mul
#align add_mem_lower_bounds_add add_mem_lowerBounds_add
-/

#print subset_lowerBounds_mul /-
@[to_additive]
theorem subset_lowerBounds_mul (s t : Set M) :
    lowerBounds s * lowerBounds t ⊆ lowerBounds (s * t) :=
  @subset_upperBounds_mul Mᵒᵈ _ _ _ _ _ _
#align subset_lower_bounds_mul subset_lowerBounds_mul
#align subset_lower_bounds_add subset_lowerBounds_add
-/

#print BddAbove.mul /-
@[to_additive]
theorem BddAbove.mul {s t : Set M} (hs : BddAbove s) (ht : BddAbove t) : BddAbove (s * t) :=
  (hs.mul ht).mono (subset_upperBounds_mul s t)
#align bdd_above.mul BddAbove.mul
#align bdd_above.add BddAbove.add
-/

#print BddBelow.mul /-
@[to_additive]
theorem BddBelow.mul {s t : Set M} (hs : BddBelow s) (ht : BddBelow t) : BddBelow (s * t) :=
  (hs.mul ht).mono (subset_lowerBounds_mul s t)
#align bdd_below.mul BddBelow.mul
#align bdd_below.add BddBelow.add
-/

end mul_add

section ConditionallyCompleteLattice

section Right

variable {ι G : Type _} [Group G] [ConditionallyCompleteLattice G]
  [CovariantClass G G (Function.swap (· * ·)) (· ≤ ·)] [Nonempty ι] {f : ι → G}

/- warning: csupr_mul -> csupᵢ_mul is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {G : Type.{u2}} [_inst_1 : Group.{u2} G] [_inst_2 : ConditionallyCompleteLattice.{u2} G] [_inst_3 : CovariantClass.{u2, u2} G G (Function.swap.{succ u2, succ u2, succ u2} G G (fun (ᾰ : G) (ᾰ : G) => G) (HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toHasMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))))) (LE.le.{u2} G (Preorder.toLE.{u2} G (PartialOrder.toPreorder.{u2} G (SemilatticeInf.toPartialOrder.{u2} G (Lattice.toSemilatticeInf.{u2} G (ConditionallyCompleteLattice.toLattice.{u2} G _inst_2))))))] [_inst_4 : Nonempty.{succ u1} ι] {f : ι -> G}, (BddAbove.{u2} G (PartialOrder.toPreorder.{u2} G (SemilatticeInf.toPartialOrder.{u2} G (Lattice.toSemilatticeInf.{u2} G (ConditionallyCompleteLattice.toLattice.{u2} G _inst_2)))) (Set.range.{u2, succ u1} G ι f)) -> (forall (a : G), Eq.{succ u2} G (HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toHasMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))) (supᵢ.{u2, succ u1} G (ConditionallyCompleteLattice.toHasSup.{u2} G _inst_2) ι (fun (i : ι) => f i)) a) (supᵢ.{u2, succ u1} G (ConditionallyCompleteLattice.toHasSup.{u2} G _inst_2) ι (fun (i : ι) => HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toHasMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))) (f i) a)))
but is expected to have type
  forall {ι : Type.{u1}} {G : Type.{u2}} [_inst_1 : Group.{u2} G] [_inst_2 : ConditionallyCompleteLattice.{u2} G] [_inst_3 : CovariantClass.{u2, u2} G G (Function.swap.{succ u2, succ u2, succ u2} G G (fun (ᾰ : G) (ᾰ : G) => G) (fun (x._@.Mathlib.Algebra.Bounds._hyg.1982 : G) (x._@.Mathlib.Algebra.Bounds._hyg.1984 : G) => HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.1982 x._@.Mathlib.Algebra.Bounds._hyg.1984)) (fun (x._@.Mathlib.Algebra.Bounds._hyg.1997 : G) (x._@.Mathlib.Algebra.Bounds._hyg.1999 : G) => LE.le.{u2} G (Preorder.toLE.{u2} G (PartialOrder.toPreorder.{u2} G (SemilatticeInf.toPartialOrder.{u2} G (Lattice.toSemilatticeInf.{u2} G (ConditionallyCompleteLattice.toLattice.{u2} G _inst_2))))) x._@.Mathlib.Algebra.Bounds._hyg.1997 x._@.Mathlib.Algebra.Bounds._hyg.1999)] [_inst_4 : Nonempty.{succ u1} ι] {f : ι -> G}, (BddAbove.{u2} G (PartialOrder.toPreorder.{u2} G (SemilatticeInf.toPartialOrder.{u2} G (Lattice.toSemilatticeInf.{u2} G (ConditionallyCompleteLattice.toLattice.{u2} G _inst_2)))) (Set.range.{u2, succ u1} G ι f)) -> (forall (a : G), Eq.{succ u2} G (HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))) (supᵢ.{u2, succ u1} G (ConditionallyCompleteLattice.toSupSet.{u2} G _inst_2) ι (fun (i : ι) => f i)) a) (supᵢ.{u2, succ u1} G (ConditionallyCompleteLattice.toSupSet.{u2} G _inst_2) ι (fun (i : ι) => HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))) (f i) a)))
Case conversion may be inaccurate. Consider using '#align csupr_mul csupᵢ_mulₓ'. -/
@[to_additive]
theorem csupᵢ_mul (hf : BddAbove (Set.range f)) (a : G) : (⨆ i, f i) * a = ⨆ i, f i * a :=
  (OrderIso.mulRight a).map_csupr hf
#align csupr_mul csupᵢ_mul
#align csupr_add csupᵢ_add

/- warning: csupr_div -> csupᵢ_div is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {G : Type.{u2}} [_inst_1 : Group.{u2} G] [_inst_2 : ConditionallyCompleteLattice.{u2} G] [_inst_3 : CovariantClass.{u2, u2} G G (Function.swap.{succ u2, succ u2, succ u2} G G (fun (ᾰ : G) (ᾰ : G) => G) (HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toHasMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))))) (LE.le.{u2} G (Preorder.toLE.{u2} G (PartialOrder.toPreorder.{u2} G (SemilatticeInf.toPartialOrder.{u2} G (Lattice.toSemilatticeInf.{u2} G (ConditionallyCompleteLattice.toLattice.{u2} G _inst_2))))))] [_inst_4 : Nonempty.{succ u1} ι] {f : ι -> G}, (BddAbove.{u2} G (PartialOrder.toPreorder.{u2} G (SemilatticeInf.toPartialOrder.{u2} G (Lattice.toSemilatticeInf.{u2} G (ConditionallyCompleteLattice.toLattice.{u2} G _inst_2)))) (Set.range.{u2, succ u1} G ι f)) -> (forall (a : G), Eq.{succ u2} G (HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G (DivInvMonoid.toHasDiv.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (supᵢ.{u2, succ u1} G (ConditionallyCompleteLattice.toHasSup.{u2} G _inst_2) ι (fun (i : ι) => f i)) a) (supᵢ.{u2, succ u1} G (ConditionallyCompleteLattice.toHasSup.{u2} G _inst_2) ι (fun (i : ι) => HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G (DivInvMonoid.toHasDiv.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (f i) a)))
but is expected to have type
  forall {ι : Type.{u1}} {G : Type.{u2}} [_inst_1 : Group.{u2} G] [_inst_2 : ConditionallyCompleteLattice.{u2} G] [_inst_3 : CovariantClass.{u2, u2} G G (Function.swap.{succ u2, succ u2, succ u2} G G (fun (ᾰ : G) (ᾰ : G) => G) (fun (x._@.Mathlib.Algebra.Bounds._hyg.2087 : G) (x._@.Mathlib.Algebra.Bounds._hyg.2089 : G) => HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.2087 x._@.Mathlib.Algebra.Bounds._hyg.2089)) (fun (x._@.Mathlib.Algebra.Bounds._hyg.2102 : G) (x._@.Mathlib.Algebra.Bounds._hyg.2104 : G) => LE.le.{u2} G (Preorder.toLE.{u2} G (PartialOrder.toPreorder.{u2} G (SemilatticeInf.toPartialOrder.{u2} G (Lattice.toSemilatticeInf.{u2} G (ConditionallyCompleteLattice.toLattice.{u2} G _inst_2))))) x._@.Mathlib.Algebra.Bounds._hyg.2102 x._@.Mathlib.Algebra.Bounds._hyg.2104)] [_inst_4 : Nonempty.{succ u1} ι] {f : ι -> G}, (BddAbove.{u2} G (PartialOrder.toPreorder.{u2} G (SemilatticeInf.toPartialOrder.{u2} G (Lattice.toSemilatticeInf.{u2} G (ConditionallyCompleteLattice.toLattice.{u2} G _inst_2)))) (Set.range.{u2, succ u1} G ι f)) -> (forall (a : G), Eq.{succ u2} G (HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G (DivInvMonoid.toDiv.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (supᵢ.{u2, succ u1} G (ConditionallyCompleteLattice.toSupSet.{u2} G _inst_2) ι (fun (i : ι) => f i)) a) (supᵢ.{u2, succ u1} G (ConditionallyCompleteLattice.toSupSet.{u2} G _inst_2) ι (fun (i : ι) => HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G (DivInvMonoid.toDiv.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (f i) a)))
Case conversion may be inaccurate. Consider using '#align csupr_div csupᵢ_divₓ'. -/
@[to_additive]
theorem csupᵢ_div (hf : BddAbove (Set.range f)) (a : G) : (⨆ i, f i) / a = ⨆ i, f i / a := by
  simp only [div_eq_mul_inv, csupᵢ_mul hf]
#align csupr_div csupᵢ_div
#align csupr_sub csupᵢ_sub

end Right

section Left

variable {ι G : Type _} [Group G] [ConditionallyCompleteLattice G]
  [CovariantClass G G (· * ·) (· ≤ ·)] [Nonempty ι] {f : ι → G}

/- warning: mul_csupr -> mul_csupᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {G : Type.{u2}} [_inst_1 : Group.{u2} G] [_inst_2 : ConditionallyCompleteLattice.{u2} G] [_inst_3 : CovariantClass.{u2, u2} G G (HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toHasMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))))) (LE.le.{u2} G (Preorder.toLE.{u2} G (PartialOrder.toPreorder.{u2} G (SemilatticeInf.toPartialOrder.{u2} G (Lattice.toSemilatticeInf.{u2} G (ConditionallyCompleteLattice.toLattice.{u2} G _inst_2))))))] [_inst_4 : Nonempty.{succ u1} ι] {f : ι -> G}, (BddAbove.{u2} G (PartialOrder.toPreorder.{u2} G (SemilatticeInf.toPartialOrder.{u2} G (Lattice.toSemilatticeInf.{u2} G (ConditionallyCompleteLattice.toLattice.{u2} G _inst_2)))) (Set.range.{u2, succ u1} G ι f)) -> (forall (a : G), Eq.{succ u2} G (HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toHasMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))) a (supᵢ.{u2, succ u1} G (ConditionallyCompleteLattice.toHasSup.{u2} G _inst_2) ι (fun (i : ι) => f i))) (supᵢ.{u2, succ u1} G (ConditionallyCompleteLattice.toHasSup.{u2} G _inst_2) ι (fun (i : ι) => HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toHasMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))) a (f i))))
but is expected to have type
  forall {ι : Type.{u1}} {G : Type.{u2}} [_inst_1 : Group.{u2} G] [_inst_2 : ConditionallyCompleteLattice.{u2} G] [_inst_3 : CovariantClass.{u2, u2} G G (fun (x._@.Mathlib.Algebra.Bounds._hyg.2247 : G) (x._@.Mathlib.Algebra.Bounds._hyg.2249 : G) => HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.2247 x._@.Mathlib.Algebra.Bounds._hyg.2249) (fun (x._@.Mathlib.Algebra.Bounds._hyg.2262 : G) (x._@.Mathlib.Algebra.Bounds._hyg.2264 : G) => LE.le.{u2} G (Preorder.toLE.{u2} G (PartialOrder.toPreorder.{u2} G (SemilatticeInf.toPartialOrder.{u2} G (Lattice.toSemilatticeInf.{u2} G (ConditionallyCompleteLattice.toLattice.{u2} G _inst_2))))) x._@.Mathlib.Algebra.Bounds._hyg.2262 x._@.Mathlib.Algebra.Bounds._hyg.2264)] [_inst_4 : Nonempty.{succ u1} ι] {f : ι -> G}, (BddAbove.{u2} G (PartialOrder.toPreorder.{u2} G (SemilatticeInf.toPartialOrder.{u2} G (Lattice.toSemilatticeInf.{u2} G (ConditionallyCompleteLattice.toLattice.{u2} G _inst_2)))) (Set.range.{u2, succ u1} G ι f)) -> (forall (a : G), Eq.{succ u2} G (HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))) a (supᵢ.{u2, succ u1} G (ConditionallyCompleteLattice.toSupSet.{u2} G _inst_2) ι (fun (i : ι) => f i))) (supᵢ.{u2, succ u1} G (ConditionallyCompleteLattice.toSupSet.{u2} G _inst_2) ι (fun (i : ι) => HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))) a (f i))))
Case conversion may be inaccurate. Consider using '#align mul_csupr mul_csupᵢₓ'. -/
@[to_additive]
theorem mul_csupᵢ (hf : BddAbove (Set.range f)) (a : G) : (a * ⨆ i, f i) = ⨆ i, a * f i :=
  (OrderIso.mulLeft a).map_csupr hf
#align mul_csupr mul_csupᵢ
#align add_csupr add_csupᵢ

end Left

end ConditionallyCompleteLattice

