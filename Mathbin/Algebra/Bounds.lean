/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module algebra.bounds
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
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

section InvNeg

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

/- warning: bdd_below_inv -> bddBelow_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] {s : Set.{u1} G}, Iff (BddBelow.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) s)) (BddAbove.{u1} G _inst_2 s)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (fun (x._@.Mathlib.Algebra.Bounds._hyg.208 : G) (x._@.Mathlib.Algebra.Bounds._hyg.210 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.208 x._@.Mathlib.Algebra.Bounds._hyg.210) (fun (x._@.Mathlib.Algebra.Bounds._hyg.223 : G) (x._@.Mathlib.Algebra.Bounds._hyg.225 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.223 x._@.Mathlib.Algebra.Bounds._hyg.225)] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (fun (x._@.Mathlib.Algebra.Bounds._hyg.245 : G) (x._@.Mathlib.Algebra.Bounds._hyg.247 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.245 x._@.Mathlib.Algebra.Bounds._hyg.247)) (fun (x._@.Mathlib.Algebra.Bounds._hyg.260 : G) (x._@.Mathlib.Algebra.Bounds._hyg.262 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.260 x._@.Mathlib.Algebra.Bounds._hyg.262)] {s : Set.{u1} G}, Iff (BddBelow.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))) s)) (BddAbove.{u1} G _inst_2 s)
Case conversion may be inaccurate. Consider using '#align bdd_below_inv bddBelow_invₓ'. -/
@[simp, to_additive]
theorem bddBelow_inv : BddBelow s⁻¹ ↔ BddAbove s :=
  (OrderIso.inv G).bdd_below_preimage
#align bdd_below_inv bddBelow_inv

/- warning: bdd_above.inv -> BddAbove.inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] {s : Set.{u1} G}, (BddAbove.{u1} G _inst_2 s) -> (BddBelow.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) s))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (fun (x._@.Mathlib.Algebra.Bounds._hyg.309 : G) (x._@.Mathlib.Algebra.Bounds._hyg.311 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.309 x._@.Mathlib.Algebra.Bounds._hyg.311) (fun (x._@.Mathlib.Algebra.Bounds._hyg.324 : G) (x._@.Mathlib.Algebra.Bounds._hyg.326 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.324 x._@.Mathlib.Algebra.Bounds._hyg.326)] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (fun (x._@.Mathlib.Algebra.Bounds._hyg.346 : G) (x._@.Mathlib.Algebra.Bounds._hyg.348 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.346 x._@.Mathlib.Algebra.Bounds._hyg.348)) (fun (x._@.Mathlib.Algebra.Bounds._hyg.361 : G) (x._@.Mathlib.Algebra.Bounds._hyg.363 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.361 x._@.Mathlib.Algebra.Bounds._hyg.363)] {s : Set.{u1} G}, (BddAbove.{u1} G _inst_2 s) -> (BddBelow.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))) s))
Case conversion may be inaccurate. Consider using '#align bdd_above.inv BddAbove.invₓ'. -/
@[to_additive]
theorem BddAbove.inv (h : BddAbove s) : BddBelow s⁻¹ :=
  bddBelow_inv.2 h
#align bdd_above.inv BddAbove.inv

/- warning: bdd_below.inv -> BddBelow.inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] {s : Set.{u1} G}, (BddBelow.{u1} G _inst_2 s) -> (BddAbove.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) s))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (fun (x._@.Mathlib.Algebra.Bounds._hyg.405 : G) (x._@.Mathlib.Algebra.Bounds._hyg.407 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.405 x._@.Mathlib.Algebra.Bounds._hyg.407) (fun (x._@.Mathlib.Algebra.Bounds._hyg.420 : G) (x._@.Mathlib.Algebra.Bounds._hyg.422 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.420 x._@.Mathlib.Algebra.Bounds._hyg.422)] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (fun (x._@.Mathlib.Algebra.Bounds._hyg.442 : G) (x._@.Mathlib.Algebra.Bounds._hyg.444 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.442 x._@.Mathlib.Algebra.Bounds._hyg.444)) (fun (x._@.Mathlib.Algebra.Bounds._hyg.457 : G) (x._@.Mathlib.Algebra.Bounds._hyg.459 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.457 x._@.Mathlib.Algebra.Bounds._hyg.459)] {s : Set.{u1} G}, (BddBelow.{u1} G _inst_2 s) -> (BddAbove.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))) s))
Case conversion may be inaccurate. Consider using '#align bdd_below.inv BddBelow.invₓ'. -/
@[to_additive]
theorem BddBelow.inv (h : BddBelow s) : BddAbove s⁻¹ :=
  bddAbove_inv.2 h
#align bdd_below.inv BddBelow.inv

/- warning: is_lub_inv -> isLUB_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] {s : Set.{u1} G} {a : G}, Iff (IsLUB.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) s) a) (IsGLB.{u1} G _inst_2 s (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (fun (x._@.Mathlib.Algebra.Bounds._hyg.498 : G) (x._@.Mathlib.Algebra.Bounds._hyg.500 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.498 x._@.Mathlib.Algebra.Bounds._hyg.500) (fun (x._@.Mathlib.Algebra.Bounds._hyg.513 : G) (x._@.Mathlib.Algebra.Bounds._hyg.515 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.513 x._@.Mathlib.Algebra.Bounds._hyg.515)] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (fun (x._@.Mathlib.Algebra.Bounds._hyg.535 : G) (x._@.Mathlib.Algebra.Bounds._hyg.537 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.535 x._@.Mathlib.Algebra.Bounds._hyg.537)) (fun (x._@.Mathlib.Algebra.Bounds._hyg.550 : G) (x._@.Mathlib.Algebra.Bounds._hyg.552 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.550 x._@.Mathlib.Algebra.Bounds._hyg.552)] {s : Set.{u1} G} {a : G}, Iff (IsLUB.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))) s) a) (IsGLB.{u1} G _inst_2 s (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align is_lub_inv isLUB_invₓ'. -/
@[simp, to_additive]
theorem isLUB_inv : IsLUB s⁻¹ a ↔ IsGLB s a⁻¹ :=
  (OrderIso.inv G).is_lub_preimage
#align is_lub_inv isLUB_inv

/- warning: is_lub_inv' -> isLUB_inv' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] {s : Set.{u1} G} {a : G}, Iff (IsLUB.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) s) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a)) (IsGLB.{u1} G _inst_2 s a)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (fun (x._@.Mathlib.Algebra.Bounds._hyg.601 : G) (x._@.Mathlib.Algebra.Bounds._hyg.603 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.601 x._@.Mathlib.Algebra.Bounds._hyg.603) (fun (x._@.Mathlib.Algebra.Bounds._hyg.616 : G) (x._@.Mathlib.Algebra.Bounds._hyg.618 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.616 x._@.Mathlib.Algebra.Bounds._hyg.618)] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (fun (x._@.Mathlib.Algebra.Bounds._hyg.638 : G) (x._@.Mathlib.Algebra.Bounds._hyg.640 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.638 x._@.Mathlib.Algebra.Bounds._hyg.640)) (fun (x._@.Mathlib.Algebra.Bounds._hyg.653 : G) (x._@.Mathlib.Algebra.Bounds._hyg.655 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.653 x._@.Mathlib.Algebra.Bounds._hyg.655)] {s : Set.{u1} G} {a : G}, Iff (IsLUB.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))) s) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a)) (IsGLB.{u1} G _inst_2 s a)
Case conversion may be inaccurate. Consider using '#align is_lub_inv' isLUB_inv'ₓ'. -/
@[to_additive]
theorem isLUB_inv' : IsLUB s⁻¹ a⁻¹ ↔ IsGLB s a :=
  (OrderIso.inv G).is_lub_preimage'
#align is_lub_inv' isLUB_inv'

/- warning: is_glb.inv -> IsGLB.inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] {s : Set.{u1} G} {a : G}, (IsGLB.{u1} G _inst_2 s a) -> (IsLUB.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) s) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (fun (x._@.Mathlib.Algebra.Bounds._hyg.707 : G) (x._@.Mathlib.Algebra.Bounds._hyg.709 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.707 x._@.Mathlib.Algebra.Bounds._hyg.709) (fun (x._@.Mathlib.Algebra.Bounds._hyg.722 : G) (x._@.Mathlib.Algebra.Bounds._hyg.724 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.722 x._@.Mathlib.Algebra.Bounds._hyg.724)] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (fun (x._@.Mathlib.Algebra.Bounds._hyg.744 : G) (x._@.Mathlib.Algebra.Bounds._hyg.746 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.744 x._@.Mathlib.Algebra.Bounds._hyg.746)) (fun (x._@.Mathlib.Algebra.Bounds._hyg.759 : G) (x._@.Mathlib.Algebra.Bounds._hyg.761 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.759 x._@.Mathlib.Algebra.Bounds._hyg.761)] {s : Set.{u1} G} {a : G}, (IsGLB.{u1} G _inst_2 s a) -> (IsLUB.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))) s) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align is_glb.inv IsGLB.invₓ'. -/
@[to_additive]
theorem IsGLB.inv (h : IsGLB s a) : IsLUB s⁻¹ a⁻¹ :=
  isLUB_inv'.2 h
#align is_glb.inv IsGLB.inv

/- warning: is_glb_inv -> isGLB_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] {s : Set.{u1} G} {a : G}, Iff (IsGLB.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) s) a) (IsLUB.{u1} G _inst_2 s (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (fun (x._@.Mathlib.Algebra.Bounds._hyg.805 : G) (x._@.Mathlib.Algebra.Bounds._hyg.807 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.805 x._@.Mathlib.Algebra.Bounds._hyg.807) (fun (x._@.Mathlib.Algebra.Bounds._hyg.820 : G) (x._@.Mathlib.Algebra.Bounds._hyg.822 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.820 x._@.Mathlib.Algebra.Bounds._hyg.822)] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (fun (x._@.Mathlib.Algebra.Bounds._hyg.842 : G) (x._@.Mathlib.Algebra.Bounds._hyg.844 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.842 x._@.Mathlib.Algebra.Bounds._hyg.844)) (fun (x._@.Mathlib.Algebra.Bounds._hyg.857 : G) (x._@.Mathlib.Algebra.Bounds._hyg.859 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.857 x._@.Mathlib.Algebra.Bounds._hyg.859)] {s : Set.{u1} G} {a : G}, Iff (IsGLB.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))) s) a) (IsLUB.{u1} G _inst_2 s (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align is_glb_inv isGLB_invₓ'. -/
@[simp, to_additive]
theorem isGLB_inv : IsGLB s⁻¹ a ↔ IsLUB s a⁻¹ :=
  (OrderIso.inv G).is_glb_preimage
#align is_glb_inv isGLB_inv

/- warning: is_glb_inv' -> isGLB_inv' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] {s : Set.{u1} G} {a : G}, Iff (IsGLB.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) s) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a)) (IsLUB.{u1} G _inst_2 s a)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (fun (x._@.Mathlib.Algebra.Bounds._hyg.908 : G) (x._@.Mathlib.Algebra.Bounds._hyg.910 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.908 x._@.Mathlib.Algebra.Bounds._hyg.910) (fun (x._@.Mathlib.Algebra.Bounds._hyg.923 : G) (x._@.Mathlib.Algebra.Bounds._hyg.925 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.923 x._@.Mathlib.Algebra.Bounds._hyg.925)] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (fun (x._@.Mathlib.Algebra.Bounds._hyg.945 : G) (x._@.Mathlib.Algebra.Bounds._hyg.947 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.945 x._@.Mathlib.Algebra.Bounds._hyg.947)) (fun (x._@.Mathlib.Algebra.Bounds._hyg.960 : G) (x._@.Mathlib.Algebra.Bounds._hyg.962 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.960 x._@.Mathlib.Algebra.Bounds._hyg.962)] {s : Set.{u1} G} {a : G}, Iff (IsGLB.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))) s) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a)) (IsLUB.{u1} G _inst_2 s a)
Case conversion may be inaccurate. Consider using '#align is_glb_inv' isGLB_inv'ₓ'. -/
@[to_additive]
theorem isGLB_inv' : IsGLB s⁻¹ a⁻¹ ↔ IsLUB s a :=
  (OrderIso.inv G).is_glb_preimage'
#align is_glb_inv' isGLB_inv'

/- warning: is_lub.inv -> IsLUB.inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))) (LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2))] {s : Set.{u1} G} {a : G}, (IsLUB.{u1} G _inst_2 s a) -> (IsGLB.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) s) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Preorder.{u1} G] [_inst_3 : CovariantClass.{u1, u1} G G (fun (x._@.Mathlib.Algebra.Bounds._hyg.1014 : G) (x._@.Mathlib.Algebra.Bounds._hyg.1016 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.1014 x._@.Mathlib.Algebra.Bounds._hyg.1016) (fun (x._@.Mathlib.Algebra.Bounds._hyg.1029 : G) (x._@.Mathlib.Algebra.Bounds._hyg.1031 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.1029 x._@.Mathlib.Algebra.Bounds._hyg.1031)] [_inst_4 : CovariantClass.{u1, u1} G G (Function.swap.{succ u1, succ u1, succ u1} G G (fun (ᾰ : G) (ᾰ : G) => G) (fun (x._@.Mathlib.Algebra.Bounds._hyg.1051 : G) (x._@.Mathlib.Algebra.Bounds._hyg.1053 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.1051 x._@.Mathlib.Algebra.Bounds._hyg.1053)) (fun (x._@.Mathlib.Algebra.Bounds._hyg.1066 : G) (x._@.Mathlib.Algebra.Bounds._hyg.1068 : G) => LE.le.{u1} G (Preorder.toLE.{u1} G _inst_2) x._@.Mathlib.Algebra.Bounds._hyg.1066 x._@.Mathlib.Algebra.Bounds._hyg.1068)] {s : Set.{u1} G} {a : G}, (IsLUB.{u1} G _inst_2 s a) -> (IsGLB.{u1} G _inst_2 (Inv.inv.{u1} (Set.{u1} G) (Set.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))) s) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align is_lub.inv IsLUB.invₓ'. -/
@[to_additive]
theorem IsLUB.inv (h : IsLUB s a) : IsGLB s⁻¹ a⁻¹ :=
  isGLB_inv'.2 h
#align is_lub.inv IsLUB.inv

end InvNeg

section mul_add

variable {M : Type _} [Mul M] [Preorder M] [CovariantClass M M (· * ·) (· ≤ ·)]
  [CovariantClass M M (swap (· * ·)) (· ≤ ·)]

#print mul_mem_upperBounds_mul /-
@[to_additive]
theorem mul_mem_upperBounds_mul {s t : Set M} {a b : M} (ha : a ∈ upperBounds s)
    (hb : b ∈ upperBounds t) : a * b ∈ upperBounds (s * t) :=
  forall_image2_iff.2 fun x hx y hy => mul_le_mul' (ha hx) (hb hy)
#align mul_mem_upper_bounds_mul mul_mem_upperBounds_mul
-/

#print subset_upperBounds_mul /-
@[to_additive]
theorem subset_upperBounds_mul (s t : Set M) :
    upperBounds s * upperBounds t ⊆ upperBounds (s * t) :=
  image2_subset_iff.2 fun x hx y hy => mul_mem_upperBounds_mul hx hy
#align subset_upper_bounds_mul subset_upperBounds_mul
-/

#print mul_mem_lowerBounds_mul /-
@[to_additive]
theorem mul_mem_lowerBounds_mul {s t : Set M} {a b : M} (ha : a ∈ lowerBounds s)
    (hb : b ∈ lowerBounds t) : a * b ∈ lowerBounds (s * t) :=
  @mul_mem_upperBounds_mul Mᵒᵈ _ _ _ _ _ _ _ _ ha hb
#align mul_mem_lower_bounds_mul mul_mem_lowerBounds_mul
-/

#print subset_lowerBounds_mul /-
@[to_additive]
theorem subset_lowerBounds_mul (s t : Set M) :
    lowerBounds s * lowerBounds t ⊆ lowerBounds (s * t) :=
  @subset_upperBounds_mul Mᵒᵈ _ _ _ _ _ _
#align subset_lower_bounds_mul subset_lowerBounds_mul
-/

#print BddAbove.mul /-
@[to_additive]
theorem BddAbove.mul {s t : Set M} (hs : BddAbove s) (ht : BddAbove t) : BddAbove (s * t) :=
  (hs.mul ht).mono (subset_upperBounds_mul s t)
#align bdd_above.mul BddAbove.mul
-/

#print BddBelow.mul /-
@[to_additive]
theorem BddBelow.mul {s t : Set M} (hs : BddBelow s) (ht : BddBelow t) : BddBelow (s * t) :=
  (hs.mul ht).mono (subset_lowerBounds_mul s t)
#align bdd_below.mul BddBelow.mul
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
  forall {ι : Type.{u1}} {G : Type.{u2}} [_inst_1 : Group.{u2} G] [_inst_2 : ConditionallyCompleteLattice.{u2} G] [_inst_3 : CovariantClass.{u2, u2} G G (Function.swap.{succ u2, succ u2, succ u2} G G (fun (ᾰ : G) (ᾰ : G) => G) (fun (x._@.Mathlib.Algebra.Bounds._hyg.1966 : G) (x._@.Mathlib.Algebra.Bounds._hyg.1968 : G) => HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.1966 x._@.Mathlib.Algebra.Bounds._hyg.1968)) (fun (x._@.Mathlib.Algebra.Bounds._hyg.1981 : G) (x._@.Mathlib.Algebra.Bounds._hyg.1983 : G) => LE.le.{u2} G (Preorder.toLE.{u2} G (PartialOrder.toPreorder.{u2} G (SemilatticeInf.toPartialOrder.{u2} G (Lattice.toSemilatticeInf.{u2} G (ConditionallyCompleteLattice.toLattice.{u2} G _inst_2))))) x._@.Mathlib.Algebra.Bounds._hyg.1981 x._@.Mathlib.Algebra.Bounds._hyg.1983)] [_inst_4 : Nonempty.{succ u1} ι] {f : ι -> G}, (BddAbove.{u2} G (PartialOrder.toPreorder.{u2} G (SemilatticeInf.toPartialOrder.{u2} G (Lattice.toSemilatticeInf.{u2} G (ConditionallyCompleteLattice.toLattice.{u2} G _inst_2)))) (Set.range.{u2, succ u1} G ι f)) -> (forall (a : G), Eq.{succ u2} G (HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))) (supᵢ.{u2, succ u1} G (ConditionallyCompleteLattice.toSupSet.{u2} G _inst_2) ι (fun (i : ι) => f i)) a) (supᵢ.{u2, succ u1} G (ConditionallyCompleteLattice.toSupSet.{u2} G _inst_2) ι (fun (i : ι) => HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))) (f i) a)))
Case conversion may be inaccurate. Consider using '#align csupr_mul csupᵢ_mulₓ'. -/
@[to_additive]
theorem csupᵢ_mul (hf : BddAbove (Set.range f)) (a : G) : (⨆ i, f i) * a = ⨆ i, f i * a :=
  (OrderIso.mulRight a).map_csupr hf
#align csupr_mul csupᵢ_mul

/- warning: csupr_div -> csupr_div is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {G : Type.{u2}} [_inst_1 : Group.{u2} G] [_inst_2 : ConditionallyCompleteLattice.{u2} G] [_inst_3 : CovariantClass.{u2, u2} G G (Function.swap.{succ u2, succ u2, succ u2} G G (fun (ᾰ : G) (ᾰ : G) => G) (HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toHasMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))))) (LE.le.{u2} G (Preorder.toLE.{u2} G (PartialOrder.toPreorder.{u2} G (SemilatticeInf.toPartialOrder.{u2} G (Lattice.toSemilatticeInf.{u2} G (ConditionallyCompleteLattice.toLattice.{u2} G _inst_2))))))] [_inst_4 : Nonempty.{succ u1} ι] {f : ι -> G}, (BddAbove.{u2} G (PartialOrder.toPreorder.{u2} G (SemilatticeInf.toPartialOrder.{u2} G (Lattice.toSemilatticeInf.{u2} G (ConditionallyCompleteLattice.toLattice.{u2} G _inst_2)))) (Set.range.{u2, succ u1} G ι f)) -> (forall (a : G), Eq.{succ u2} G (HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G (DivInvMonoid.toHasDiv.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (supᵢ.{u2, succ u1} G (ConditionallyCompleteLattice.toHasSup.{u2} G _inst_2) ι (fun (i : ι) => f i)) a) (supᵢ.{u2, succ u1} G (ConditionallyCompleteLattice.toHasSup.{u2} G _inst_2) ι (fun (i : ι) => HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G (DivInvMonoid.toHasDiv.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (f i) a)))
but is expected to have type
  forall {ι : Type.{u1}} {G : Type.{u2}} [_inst_1 : Group.{u2} G] [_inst_2 : ConditionallyCompleteLattice.{u2} G] [_inst_3 : CovariantClass.{u2, u2} G G (Function.swap.{succ u2, succ u2, succ u2} G G (fun (ᾰ : G) (ᾰ : G) => G) (fun (x._@.Mathlib.Algebra.Bounds._hyg.2078 : G) (x._@.Mathlib.Algebra.Bounds._hyg.2080 : G) => HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.2078 x._@.Mathlib.Algebra.Bounds._hyg.2080)) (fun (x._@.Mathlib.Algebra.Bounds._hyg.2093 : G) (x._@.Mathlib.Algebra.Bounds._hyg.2095 : G) => LE.le.{u2} G (Preorder.toLE.{u2} G (PartialOrder.toPreorder.{u2} G (SemilatticeInf.toPartialOrder.{u2} G (Lattice.toSemilatticeInf.{u2} G (ConditionallyCompleteLattice.toLattice.{u2} G _inst_2))))) x._@.Mathlib.Algebra.Bounds._hyg.2093 x._@.Mathlib.Algebra.Bounds._hyg.2095)] [_inst_4 : Nonempty.{succ u1} ι] {f : ι -> G}, (BddAbove.{u2} G (PartialOrder.toPreorder.{u2} G (SemilatticeInf.toPartialOrder.{u2} G (Lattice.toSemilatticeInf.{u2} G (ConditionallyCompleteLattice.toLattice.{u2} G _inst_2)))) (Set.range.{u2, succ u1} G ι f)) -> (forall (a : G), Eq.{succ u2} G (HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G (DivInvMonoid.toDiv.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (supᵢ.{u2, succ u1} G (ConditionallyCompleteLattice.toSupSet.{u2} G _inst_2) ι (fun (i : ι) => f i)) a) (supᵢ.{u2, succ u1} G (ConditionallyCompleteLattice.toSupSet.{u2} G _inst_2) ι (fun (i : ι) => HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G (DivInvMonoid.toDiv.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (f i) a)))
Case conversion may be inaccurate. Consider using '#align csupr_div csupr_divₓ'. -/
@[to_additive]
theorem csupr_div (hf : BddAbove (Set.range f)) (a : G) : (⨆ i, f i) / a = ⨆ i, f i / a := by
  simp only [div_eq_mul_inv, csupᵢ_mul hf]
#align csupr_div csupr_div

end Right

section Left

variable {ι G : Type _} [Group G] [ConditionallyCompleteLattice G]
  [CovariantClass G G (· * ·) (· ≤ ·)] [Nonempty ι] {f : ι → G}

/- warning: mul_csupr -> mul_csupᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {G : Type.{u2}} [_inst_1 : Group.{u2} G] [_inst_2 : ConditionallyCompleteLattice.{u2} G] [_inst_3 : CovariantClass.{u2, u2} G G (HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toHasMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))))) (LE.le.{u2} G (Preorder.toLE.{u2} G (PartialOrder.toPreorder.{u2} G (SemilatticeInf.toPartialOrder.{u2} G (Lattice.toSemilatticeInf.{u2} G (ConditionallyCompleteLattice.toLattice.{u2} G _inst_2))))))] [_inst_4 : Nonempty.{succ u1} ι] {f : ι -> G}, (BddAbove.{u2} G (PartialOrder.toPreorder.{u2} G (SemilatticeInf.toPartialOrder.{u2} G (Lattice.toSemilatticeInf.{u2} G (ConditionallyCompleteLattice.toLattice.{u2} G _inst_2)))) (Set.range.{u2, succ u1} G ι f)) -> (forall (a : G), Eq.{succ u2} G (HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toHasMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))) a (supᵢ.{u2, succ u1} G (ConditionallyCompleteLattice.toHasSup.{u2} G _inst_2) ι (fun (i : ι) => f i))) (supᵢ.{u2, succ u1} G (ConditionallyCompleteLattice.toHasSup.{u2} G _inst_2) ι (fun (i : ι) => HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toHasMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))) a (f i))))
but is expected to have type
  forall {ι : Type.{u1}} {G : Type.{u2}} [_inst_1 : Group.{u2} G] [_inst_2 : ConditionallyCompleteLattice.{u2} G] [_inst_3 : CovariantClass.{u2, u2} G G (fun (x._@.Mathlib.Algebra.Bounds._hyg.2245 : G) (x._@.Mathlib.Algebra.Bounds._hyg.2247 : G) => HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))) x._@.Mathlib.Algebra.Bounds._hyg.2245 x._@.Mathlib.Algebra.Bounds._hyg.2247) (fun (x._@.Mathlib.Algebra.Bounds._hyg.2260 : G) (x._@.Mathlib.Algebra.Bounds._hyg.2262 : G) => LE.le.{u2} G (Preorder.toLE.{u2} G (PartialOrder.toPreorder.{u2} G (SemilatticeInf.toPartialOrder.{u2} G (Lattice.toSemilatticeInf.{u2} G (ConditionallyCompleteLattice.toLattice.{u2} G _inst_2))))) x._@.Mathlib.Algebra.Bounds._hyg.2260 x._@.Mathlib.Algebra.Bounds._hyg.2262)] [_inst_4 : Nonempty.{succ u1} ι] {f : ι -> G}, (BddAbove.{u2} G (PartialOrder.toPreorder.{u2} G (SemilatticeInf.toPartialOrder.{u2} G (Lattice.toSemilatticeInf.{u2} G (ConditionallyCompleteLattice.toLattice.{u2} G _inst_2)))) (Set.range.{u2, succ u1} G ι f)) -> (forall (a : G), Eq.{succ u2} G (HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))) a (supᵢ.{u2, succ u1} G (ConditionallyCompleteLattice.toSupSet.{u2} G _inst_2) ι (fun (i : ι) => f i))) (supᵢ.{u2, succ u1} G (ConditionallyCompleteLattice.toSupSet.{u2} G _inst_2) ι (fun (i : ι) => HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))) a (f i))))
Case conversion may be inaccurate. Consider using '#align mul_csupr mul_csupᵢₓ'. -/
@[to_additive]
theorem mul_csupᵢ (hf : BddAbove (Set.range f)) (a : G) : (a * ⨆ i, f i) = ⨆ i, a * f i :=
  (OrderIso.mulLeft a).map_csupr hf
#align mul_csupr mul_csupᵢ

end Left

end ConditionallyCompleteLattice

