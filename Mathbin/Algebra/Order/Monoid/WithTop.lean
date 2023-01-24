/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.monoid.with_top
! leanprover-community/mathlib commit 8631e2d5ea77f6c13054d9151d82b83069680cb1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.Group
import Mathbin.Algebra.Order.Monoid.OrderDual
import Mathbin.Algebra.Order.Monoid.WithZero.Basic
import Mathbin.Data.Nat.Cast.Defs

/-! # Adjoining top/bottom elements to ordered monoids.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/


universe u v

variable {α : Type u} {β : Type v}

open Function

namespace WithTop

section One

variable [One α]

@[to_additive]
instance : One (WithTop α) :=
  ⟨(1 : α)⟩

#print WithTop.coe_one /-
@[simp, norm_cast, to_additive]
theorem coe_one : ((1 : α) : WithTop α) = 1 :=
  rfl
#align with_top.coe_one WithTop.coe_one
#align with_top.coe_zero WithTop.coe_zero
-/

#print WithTop.coe_eq_one /-
@[simp, norm_cast, to_additive]
theorem coe_eq_one {a : α} : (a : WithTop α) = 1 ↔ a = 1 :=
  coe_eq_coe
#align with_top.coe_eq_one WithTop.coe_eq_one
#align with_top.coe_eq_zero WithTop.coe_eq_zero
-/

/- warning: with_top.one_lt_coe -> WithTop.one_lt_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : One.{u1} α] [_inst_2 : LT.{u1} α] {a : α}, Iff (LT.lt.{u1} (WithTop.{u1} α) (WithTop.hasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} (WithTop.{u1} α) 1 (OfNat.mk.{u1} (WithTop.{u1} α) 1 (One.one.{u1} (WithTop.{u1} α) (WithTop.one.{u1} α _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) a)) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_1))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : One.{u1} α] [_inst_2 : LT.{u1} α] {a : α}, Iff (LT.lt.{u1} (WithTop.{u1} α) (WithTop.lt.{u1} α _inst_2) (OfNat.ofNat.{u1} (WithTop.{u1} α) 1 (One.toOfNat1.{u1} (WithTop.{u1} α) (WithTop.one.{u1} α _inst_1))) (WithTop.some.{u1} α a)) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α _inst_1)) a)
Case conversion may be inaccurate. Consider using '#align with_top.one_lt_coe WithTop.one_lt_coeₓ'. -/
@[simp, norm_cast, to_additive coe_pos]
theorem one_lt_coe [LT α] {a : α} : 1 < (a : WithTop α) ↔ 1 < a :=
  coe_lt_coe
#align with_top.one_lt_coe WithTop.one_lt_coe
#align with_top.coe_pos WithTop.coe_pos

/- warning: with_top.coe_lt_one -> WithTop.coe_lt_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : One.{u1} α] [_inst_2 : LT.{u1} α] {a : α}, Iff (LT.lt.{u1} (WithTop.{u1} α) (WithTop.hasLt.{u1} α _inst_2) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) a) (OfNat.ofNat.{u1} (WithTop.{u1} α) 1 (OfNat.mk.{u1} (WithTop.{u1} α) 1 (One.one.{u1} (WithTop.{u1} α) (WithTop.one.{u1} α _inst_1))))) (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : One.{u1} α] [_inst_2 : LT.{u1} α] {a : α}, Iff (LT.lt.{u1} (WithTop.{u1} α) (WithTop.lt.{u1} α _inst_2) (WithTop.some.{u1} α a) (OfNat.ofNat.{u1} (WithTop.{u1} α) 1 (One.toOfNat1.{u1} (WithTop.{u1} α) (WithTop.one.{u1} α _inst_1)))) (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align with_top.coe_lt_one WithTop.coe_lt_oneₓ'. -/
@[simp, norm_cast, to_additive coe_lt_zero]
theorem coe_lt_one [LT α] {a : α} : (a : WithTop α) < 1 ↔ a < 1 :=
  coe_lt_coe
#align with_top.coe_lt_one WithTop.coe_lt_one
#align with_top.coe_lt_zero WithTop.coe_lt_zero

/- warning: with_top.map_one -> WithTop.map_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : One.{u1} α] {β : Type.{u2}} (f : α -> β), Eq.{succ u2} (WithTop.{u2} β) (WithTop.map.{u1, u2} α β f (OfNat.ofNat.{u1} (WithTop.{u1} α) 1 (OfNat.mk.{u1} (WithTop.{u1} α) 1 (One.one.{u1} (WithTop.{u1} α) (WithTop.one.{u1} α _inst_1))))) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) β (WithTop.{u2} β) (HasLiftT.mk.{succ u2, succ u2} β (WithTop.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} β (WithTop.{u2} β) (WithTop.hasCoeT.{u2} β))) (f (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : One.{u2} α] {β : Type.{u1}} (f : α -> β), Eq.{succ u1} (WithTop.{u1} β) (WithTop.map.{u2, u1} α β f (OfNat.ofNat.{u2} (WithTop.{u2} α) 1 (One.toOfNat1.{u2} (WithTop.{u2} α) (WithTop.one.{u2} α _inst_1)))) (WithTop.some.{u1} β (f (OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align with_top.map_one WithTop.map_oneₓ'. -/
@[simp, to_additive]
protected theorem map_one {β} (f : α → β) : (1 : WithTop α).map f = (f 1 : WithTop β) :=
  rfl
#align with_top.map_one WithTop.map_one
#align with_top.map_zero WithTop.map_zero

#print WithTop.one_eq_coe /-
@[simp, norm_cast, to_additive]
theorem one_eq_coe {a : α} : 1 = (a : WithTop α) ↔ a = 1 :=
  trans eq_comm coe_eq_one
#align with_top.one_eq_coe WithTop.one_eq_coe
#align with_top.zero_eq_coe WithTop.zero_eq_coe
-/

#print WithTop.top_ne_one /-
@[simp, to_additive]
theorem top_ne_one : ⊤ ≠ (1 : WithTop α) :=
  fun.
#align with_top.top_ne_one WithTop.top_ne_one
#align with_top.top_ne_zero WithTop.top_ne_zero
-/

#print WithTop.one_ne_top /-
@[simp, to_additive]
theorem one_ne_top : (1 : WithTop α) ≠ ⊤ :=
  fun.
#align with_top.one_ne_top WithTop.one_ne_top
#align with_top.zero_ne_top WithTop.zero_ne_top
-/

instance [Zero α] [LE α] [ZeroLEOneClass α] : ZeroLEOneClass (WithTop α) :=
  ⟨some_le_some.2 zero_le_one⟩

end One

section Add

variable [Add α] {a b c d : WithTop α} {x y : α}

instance : Add (WithTop α) :=
  ⟨Option.map₂ (· + ·)⟩

#print WithTop.coe_add /-
@[norm_cast]
theorem coe_add : ((x + y : α) : WithTop α) = x + y :=
  rfl
#align with_top.coe_add WithTop.coe_add
-/

#print WithTop.coe_bit0 /-
@[norm_cast]
theorem coe_bit0 : ((bit0 x : α) : WithTop α) = bit0 x :=
  rfl
#align with_top.coe_bit0 WithTop.coe_bit0
-/

#print WithTop.coe_bit1 /-
@[norm_cast]
theorem coe_bit1 [One α] {a : α} : ((bit1 a : α) : WithTop α) = bit1 a :=
  rfl
#align with_top.coe_bit1 WithTop.coe_bit1
-/

#print WithTop.top_add /-
@[simp]
theorem top_add (a : WithTop α) : ⊤ + a = ⊤ :=
  rfl
#align with_top.top_add WithTop.top_add
-/

#print WithTop.add_top /-
@[simp]
theorem add_top (a : WithTop α) : a + ⊤ = ⊤ := by cases a <;> rfl
#align with_top.add_top WithTop.add_top
-/

#print WithTop.add_eq_top /-
@[simp]
theorem add_eq_top : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := by
  cases a <;> cases b <;> simp [none_eq_top, some_eq_coe, ← WithTop.coe_add]
#align with_top.add_eq_top WithTop.add_eq_top
-/

#print WithTop.add_ne_top /-
theorem add_ne_top : a + b ≠ ⊤ ↔ a ≠ ⊤ ∧ b ≠ ⊤ :=
  add_eq_top.Not.trans not_or
#align with_top.add_ne_top WithTop.add_ne_top
-/

#print WithTop.add_lt_top /-
theorem add_lt_top [PartialOrder α] {a b : WithTop α} : a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤ := by
  simp_rw [lt_top_iff_ne_top, add_ne_top]
#align with_top.add_lt_top WithTop.add_lt_top
-/

#print WithTop.add_eq_coe /-
theorem add_eq_coe :
    ∀ {a b : WithTop α} {c : α}, a + b = c ↔ ∃ a' b' : α, ↑a' = a ∧ ↑b' = b ∧ a' + b' = c
  | none, b, c => by simp [none_eq_top]
  | some a, none, c => by simp [none_eq_top]
  | some a, some b, c => by
    simp only [some_eq_coe, ← coe_add, coe_eq_coe, exists_and_left, exists_eq_left]
#align with_top.add_eq_coe WithTop.add_eq_coe
-/

#print WithTop.add_coe_eq_top_iff /-
@[simp]
theorem add_coe_eq_top_iff {x : WithTop α} {y : α} : x + y = ⊤ ↔ x = ⊤ := by
  induction x using WithTop.recTopCoe <;> simp [← coe_add]
#align with_top.add_coe_eq_top_iff WithTop.add_coe_eq_top_iff
-/

#print WithTop.coe_add_eq_top_iff /-
@[simp]
theorem coe_add_eq_top_iff {y : WithTop α} : ↑x + y = ⊤ ↔ y = ⊤ := by
  induction y using WithTop.recTopCoe <;> simp [← coe_add]
#align with_top.coe_add_eq_top_iff WithTop.coe_add_eq_top_iff
-/

/- warning: with_top.covariant_class_add_le -> WithTop.covariantClass_add_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1)) (LE.le.{u1} α _inst_2)], CovariantClass.{u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1))) (LE.le.{u1} (WithTop.{u1} α) (WithTop.hasLe.{u1} α _inst_2))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1123 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1125 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1123 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1125) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1138 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1140 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1138 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1140)], CovariantClass.{u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1162 : WithTop.{u1} α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1164 : WithTop.{u1} α) => HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1162 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1164) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1177 : WithTop.{u1} α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1179 : WithTop.{u1} α) => LE.le.{u1} (WithTop.{u1} α) (WithTop.le.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1177 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1179)
Case conversion may be inaccurate. Consider using '#align with_top.covariant_class_add_le WithTop.covariantClass_add_leₓ'. -/
instance covariantClass_add_le [LE α] [CovariantClass α α (· + ·) (· ≤ ·)] :
    CovariantClass (WithTop α) (WithTop α) (· + ·) (· ≤ ·) :=
  ⟨fun a b c h => by
    cases a <;> cases c <;> try exact le_top
    rcases le_coe_iff.1 h with ⟨b, rfl, h'⟩
    exact coe_le_coe.2 (add_le_add_left (coe_le_coe.1 h) _)⟩
#align with_top.covariant_class_add_le WithTop.covariantClass_add_le

/- warning: with_top.covariant_class_swap_add_le -> WithTop.covariantClass_swap_add_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1))) (LE.le.{u1} α _inst_2)], CovariantClass.{u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (Function.swap.{succ u1, succ u1, succ u1} (WithTop.{u1} α) (WithTop.{u1} α) (fun (ᾰ : WithTop.{u1} α) (ᾰ : WithTop.{u1} α) => WithTop.{u1} α) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)))) (LE.le.{u1} (WithTop.{u1} α) (WithTop.hasLe.{u1} α _inst_2))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1318 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1320 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1318 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1320)) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1333 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1335 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1333 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1335)], CovariantClass.{u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (Function.swap.{succ u1, succ u1, succ u1} (WithTop.{u1} α) (WithTop.{u1} α) (fun (ᾰ : WithTop.{u1} α) (ᾰ : WithTop.{u1} α) => WithTop.{u1} α) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1360 : WithTop.{u1} α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1362 : WithTop.{u1} α) => HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1360 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1362)) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1375 : WithTop.{u1} α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1377 : WithTop.{u1} α) => LE.le.{u1} (WithTop.{u1} α) (WithTop.le.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1375 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1377)
Case conversion may be inaccurate. Consider using '#align with_top.covariant_class_swap_add_le WithTop.covariantClass_swap_add_leₓ'. -/
instance covariantClass_swap_add_le [LE α] [CovariantClass α α (swap (· + ·)) (· ≤ ·)] :
    CovariantClass (WithTop α) (WithTop α) (swap (· + ·)) (· ≤ ·) :=
  ⟨fun a b c h => by
    cases a <;> cases c <;> try exact le_top
    rcases le_coe_iff.1 h with ⟨b, rfl, h'⟩
    exact coe_le_coe.2 (add_le_add_right (coe_le_coe.1 h) _)⟩
#align with_top.covariant_class_swap_add_le WithTop.covariantClass_swap_add_le

/- warning: with_top.contravariant_class_add_lt -> WithTop.contravariantClass_add_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1)) (LT.lt.{u1} α _inst_2)], ContravariantClass.{u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1))) (LT.lt.{u1} (WithTop.{u1} α) (WithTop.hasLt.{u1} α _inst_2))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1513 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1515 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1513 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1515) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1528 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1530 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1528 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1530)], ContravariantClass.{u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1552 : WithTop.{u1} α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1554 : WithTop.{u1} α) => HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1552 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1554) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1567 : WithTop.{u1} α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1569 : WithTop.{u1} α) => LT.lt.{u1} (WithTop.{u1} α) (WithTop.lt.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1567 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1569)
Case conversion may be inaccurate. Consider using '#align with_top.contravariant_class_add_lt WithTop.contravariantClass_add_ltₓ'. -/
instance contravariantClass_add_lt [LT α] [ContravariantClass α α (· + ·) (· < ·)] :
    ContravariantClass (WithTop α) (WithTop α) (· + ·) (· < ·) :=
  ⟨fun a b c h => by
    induction a using WithTop.recTopCoe; · exact (not_none_lt _ h).elim
    induction b using WithTop.recTopCoe; · exact (not_none_lt _ h).elim
    induction c using WithTop.recTopCoe
    · exact coe_lt_top _
    · exact coe_lt_coe.2 (lt_of_add_lt_add_left <| coe_lt_coe.1 h)⟩
#align with_top.contravariant_class_add_lt WithTop.contravariantClass_add_lt

/- warning: with_top.contravariant_class_swap_add_lt -> WithTop.contravariantClass_swap_add_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1))) (LT.lt.{u1} α _inst_2)], ContravariantClass.{u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (Function.swap.{succ u1, succ u1, succ u1} (WithTop.{u1} α) (WithTop.{u1} α) (fun (ᾰ : WithTop.{u1} α) (ᾰ : WithTop.{u1} α) => WithTop.{u1} α) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)))) (LT.lt.{u1} (WithTop.{u1} α) (WithTop.hasLt.{u1} α _inst_2))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1663 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1665 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1663 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1665)) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1678 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1680 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1678 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1680)], ContravariantClass.{u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (Function.swap.{succ u1, succ u1, succ u1} (WithTop.{u1} α) (WithTop.{u1} α) (fun (ᾰ : WithTop.{u1} α) (ᾰ : WithTop.{u1} α) => WithTop.{u1} α) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1705 : WithTop.{u1} α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1707 : WithTop.{u1} α) => HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1705 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1707)) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1720 : WithTop.{u1} α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1722 : WithTop.{u1} α) => LT.lt.{u1} (WithTop.{u1} α) (WithTop.lt.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1720 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1722)
Case conversion may be inaccurate. Consider using '#align with_top.contravariant_class_swap_add_lt WithTop.contravariantClass_swap_add_ltₓ'. -/
instance contravariantClass_swap_add_lt [LT α] [ContravariantClass α α (swap (· + ·)) (· < ·)] :
    ContravariantClass (WithTop α) (WithTop α) (swap (· + ·)) (· < ·) :=
  ⟨fun a b c h => by
    cases a <;> cases b <;> try exact (not_none_lt _ h).elim
    cases c
    · exact coe_lt_top _
    · exact coe_lt_coe.2 (lt_of_add_lt_add_right <| coe_lt_coe.1 h)⟩
#align with_top.contravariant_class_swap_add_lt WithTop.contravariantClass_swap_add_lt

/- warning: with_top.le_of_add_le_add_left -> WithTop.le_of_add_le_add_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] {a : WithTop.{u1} α} {b : WithTop.{u1} α} {c : WithTop.{u1} α} [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1)) (LE.le.{u1} α _inst_2)], (Ne.{succ u1} (WithTop.{u1} α) a (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) -> (LE.le.{u1} (WithTop.{u1} α) (WithTop.hasLe.{u1} α _inst_2) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) a b) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) a c)) -> (LE.le.{u1} (WithTop.{u1} α) (WithTop.hasLe.{u1} α _inst_2) b c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] {a : WithTop.{u1} α} {b : WithTop.{u1} α} {c : WithTop.{u1} α} [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1883 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1885 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1883 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1885) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1898 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1900 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1898 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.1900)], (Ne.{succ u1} (WithTop.{u1} α) a (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))) -> (LE.le.{u1} (WithTop.{u1} α) (WithTop.le.{u1} α _inst_2) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) a b) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) a c)) -> (LE.le.{u1} (WithTop.{u1} α) (WithTop.le.{u1} α _inst_2) b c)
Case conversion may be inaccurate. Consider using '#align with_top.le_of_add_le_add_left WithTop.le_of_add_le_add_leftₓ'. -/
protected theorem le_of_add_le_add_left [LE α] [ContravariantClass α α (· + ·) (· ≤ ·)] (ha : a ≠ ⊤)
    (h : a + b ≤ a + c) : b ≤ c := by
  lift a to α using ha
  induction c using WithTop.recTopCoe; · exact le_top
  induction b using WithTop.recTopCoe; · exact (not_top_le_coe _ h).elim
  simp only [← coe_add, coe_le_coe] at h⊢
  exact le_of_add_le_add_left h
#align with_top.le_of_add_le_add_left WithTop.le_of_add_le_add_left

/- warning: with_top.le_of_add_le_add_right -> WithTop.le_of_add_le_add_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] {a : WithTop.{u1} α} {b : WithTop.{u1} α} {c : WithTop.{u1} α} [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1))) (LE.le.{u1} α _inst_2)], (Ne.{succ u1} (WithTop.{u1} α) a (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) -> (LE.le.{u1} (WithTop.{u1} α) (WithTop.hasLe.{u1} α _inst_2) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) b a) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) c a)) -> (LE.le.{u1} (WithTop.{u1} α) (WithTop.hasLe.{u1} α _inst_2) b c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] {a : WithTop.{u1} α} {b : WithTop.{u1} α} {c : WithTop.{u1} α} [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2010 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2012 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2010 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2012)) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2025 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2027 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2025 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2027)], (Ne.{succ u1} (WithTop.{u1} α) a (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))) -> (LE.le.{u1} (WithTop.{u1} α) (WithTop.le.{u1} α _inst_2) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) b a) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) c a)) -> (LE.le.{u1} (WithTop.{u1} α) (WithTop.le.{u1} α _inst_2) b c)
Case conversion may be inaccurate. Consider using '#align with_top.le_of_add_le_add_right WithTop.le_of_add_le_add_rightₓ'. -/
protected theorem le_of_add_le_add_right [LE α] [ContravariantClass α α (swap (· + ·)) (· ≤ ·)]
    (ha : a ≠ ⊤) (h : b + a ≤ c + a) : b ≤ c :=
  by
  lift a to α using ha
  cases c
  · exact le_top
  cases b
  · exact (not_top_le_coe _ h).elim
  · exact coe_le_coe.2 (le_of_add_le_add_right <| coe_le_coe.1 h)
#align with_top.le_of_add_le_add_right WithTop.le_of_add_le_add_right

/- warning: with_top.add_lt_add_left -> WithTop.add_lt_add_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] {a : WithTop.{u1} α} {b : WithTop.{u1} α} {c : WithTop.{u1} α} [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1)) (LT.lt.{u1} α _inst_2)], (Ne.{succ u1} (WithTop.{u1} α) a (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) -> (LT.lt.{u1} (WithTop.{u1} α) (WithTop.hasLt.{u1} α _inst_2) b c) -> (LT.lt.{u1} (WithTop.{u1} α) (WithTop.hasLt.{u1} α _inst_2) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) a b) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] {a : WithTop.{u1} α} {b : WithTop.{u1} α} {c : WithTop.{u1} α} [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2145 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2147 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2145 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2147) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2160 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2162 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2160 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2162)], (Ne.{succ u1} (WithTop.{u1} α) a (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))) -> (LT.lt.{u1} (WithTop.{u1} α) (WithTop.lt.{u1} α _inst_2) b c) -> (LT.lt.{u1} (WithTop.{u1} α) (WithTop.lt.{u1} α _inst_2) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) a b) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) a c))
Case conversion may be inaccurate. Consider using '#align with_top.add_lt_add_left WithTop.add_lt_add_leftₓ'. -/
protected theorem add_lt_add_left [LT α] [CovariantClass α α (· + ·) (· < ·)] (ha : a ≠ ⊤)
    (h : b < c) : a + b < a + c := by
  lift a to α using ha
  rcases lt_iff_exists_coe.1 h with ⟨b, rfl, h'⟩
  cases c
  · exact coe_lt_top _
  · exact coe_lt_coe.2 (add_lt_add_left (coe_lt_coe.1 h) _)
#align with_top.add_lt_add_left WithTop.add_lt_add_left

/- warning: with_top.add_lt_add_right -> WithTop.add_lt_add_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] {a : WithTop.{u1} α} {b : WithTop.{u1} α} {c : WithTop.{u1} α} [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1))) (LT.lt.{u1} α _inst_2)], (Ne.{succ u1} (WithTop.{u1} α) a (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) -> (LT.lt.{u1} (WithTop.{u1} α) (WithTop.hasLt.{u1} α _inst_2) b c) -> (LT.lt.{u1} (WithTop.{u1} α) (WithTop.hasLt.{u1} α _inst_2) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) b a) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] {a : WithTop.{u1} α} {b : WithTop.{u1} α} {c : WithTop.{u1} α} [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2274 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2276 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2274 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2276)) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2289 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2291 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2289 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2291)], (Ne.{succ u1} (WithTop.{u1} α) a (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))) -> (LT.lt.{u1} (WithTop.{u1} α) (WithTop.lt.{u1} α _inst_2) b c) -> (LT.lt.{u1} (WithTop.{u1} α) (WithTop.lt.{u1} α _inst_2) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) b a) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) c a))
Case conversion may be inaccurate. Consider using '#align with_top.add_lt_add_right WithTop.add_lt_add_rightₓ'. -/
protected theorem add_lt_add_right [LT α] [CovariantClass α α (swap (· + ·)) (· < ·)] (ha : a ≠ ⊤)
    (h : b < c) : b + a < c + a := by
  lift a to α using ha
  rcases lt_iff_exists_coe.1 h with ⟨b, rfl, h'⟩
  cases c
  · exact coe_lt_top _
  · exact coe_lt_coe.2 (add_lt_add_right (coe_lt_coe.1 h) _)
#align with_top.add_lt_add_right WithTop.add_lt_add_right

/- warning: with_top.add_le_add_iff_left -> WithTop.add_le_add_iff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] {a : WithTop.{u1} α} {b : WithTop.{u1} α} {c : WithTop.{u1} α} [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1)) (LE.le.{u1} α _inst_2)] [_inst_4 : ContravariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1)) (LE.le.{u1} α _inst_2)], (Ne.{succ u1} (WithTop.{u1} α) a (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) -> (Iff (LE.le.{u1} (WithTop.{u1} α) (WithTop.hasLe.{u1} α _inst_2) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) a b) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) a c)) (LE.le.{u1} (WithTop.{u1} α) (WithTop.hasLe.{u1} α _inst_2) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] {a : WithTop.{u1} α} {b : WithTop.{u1} α} {c : WithTop.{u1} α} [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2400 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2402 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2400 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2402) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2415 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2417 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2415 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2417)] [_inst_4 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2434 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2436 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2434 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2436) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2449 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2451 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2449 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2451)], (Ne.{succ u1} (WithTop.{u1} α) a (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))) -> (Iff (LE.le.{u1} (WithTop.{u1} α) (WithTop.le.{u1} α _inst_2) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) a b) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) a c)) (LE.le.{u1} (WithTop.{u1} α) (WithTop.le.{u1} α _inst_2) b c))
Case conversion may be inaccurate. Consider using '#align with_top.add_le_add_iff_left WithTop.add_le_add_iff_leftₓ'. -/
protected theorem add_le_add_iff_left [LE α] [CovariantClass α α (· + ·) (· ≤ ·)]
    [ContravariantClass α α (· + ·) (· ≤ ·)] (ha : a ≠ ⊤) : a + b ≤ a + c ↔ b ≤ c :=
  ⟨WithTop.le_of_add_le_add_left ha, fun h => add_le_add_left h a⟩
#align with_top.add_le_add_iff_left WithTop.add_le_add_iff_left

/- warning: with_top.add_le_add_iff_right -> WithTop.add_le_add_iff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] {a : WithTop.{u1} α} {b : WithTop.{u1} α} {c : WithTop.{u1} α} [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1))) (LE.le.{u1} α _inst_2)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1))) (LE.le.{u1} α _inst_2)], (Ne.{succ u1} (WithTop.{u1} α) a (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) -> (Iff (LE.le.{u1} (WithTop.{u1} α) (WithTop.hasLe.{u1} α _inst_2) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) b a) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) c a)) (LE.le.{u1} (WithTop.{u1} α) (WithTop.hasLe.{u1} α _inst_2) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] {a : WithTop.{u1} α} {b : WithTop.{u1} α} {c : WithTop.{u1} α} [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2525 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2527 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2525 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2527)) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2540 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2542 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2540 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2542)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2562 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2564 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2562 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2564)) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2577 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2579 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2577 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2579)], (Ne.{succ u1} (WithTop.{u1} α) a (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))) -> (Iff (LE.le.{u1} (WithTop.{u1} α) (WithTop.le.{u1} α _inst_2) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) b a) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) c a)) (LE.le.{u1} (WithTop.{u1} α) (WithTop.le.{u1} α _inst_2) b c))
Case conversion may be inaccurate. Consider using '#align with_top.add_le_add_iff_right WithTop.add_le_add_iff_rightₓ'. -/
protected theorem add_le_add_iff_right [LE α] [CovariantClass α α (swap (· + ·)) (· ≤ ·)]
    [ContravariantClass α α (swap (· + ·)) (· ≤ ·)] (ha : a ≠ ⊤) : b + a ≤ c + a ↔ b ≤ c :=
  ⟨WithTop.le_of_add_le_add_right ha, fun h => add_le_add_right h a⟩
#align with_top.add_le_add_iff_right WithTop.add_le_add_iff_right

/- warning: with_top.add_lt_add_iff_left -> WithTop.add_lt_add_iff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] {a : WithTop.{u1} α} {b : WithTop.{u1} α} {c : WithTop.{u1} α} [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1)) (LT.lt.{u1} α _inst_2)] [_inst_4 : ContravariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1)) (LT.lt.{u1} α _inst_2)], (Ne.{succ u1} (WithTop.{u1} α) a (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) -> (Iff (LT.lt.{u1} (WithTop.{u1} α) (WithTop.hasLt.{u1} α _inst_2) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) a b) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) a c)) (LT.lt.{u1} (WithTop.{u1} α) (WithTop.hasLt.{u1} α _inst_2) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] {a : WithTop.{u1} α} {b : WithTop.{u1} α} {c : WithTop.{u1} α} [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2650 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2652 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2650 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2652) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2665 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2667 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2665 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2667)] [_inst_4 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2684 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2686 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2684 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2686) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2699 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2701 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2699 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2701)], (Ne.{succ u1} (WithTop.{u1} α) a (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))) -> (Iff (LT.lt.{u1} (WithTop.{u1} α) (WithTop.lt.{u1} α _inst_2) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) a b) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) a c)) (LT.lt.{u1} (WithTop.{u1} α) (WithTop.lt.{u1} α _inst_2) b c))
Case conversion may be inaccurate. Consider using '#align with_top.add_lt_add_iff_left WithTop.add_lt_add_iff_leftₓ'. -/
protected theorem add_lt_add_iff_left [LT α] [CovariantClass α α (· + ·) (· < ·)]
    [ContravariantClass α α (· + ·) (· < ·)] (ha : a ≠ ⊤) : a + b < a + c ↔ b < c :=
  ⟨lt_of_add_lt_add_left, WithTop.add_lt_add_left ha⟩
#align with_top.add_lt_add_iff_left WithTop.add_lt_add_iff_left

/- warning: with_top.add_lt_add_iff_right -> WithTop.add_lt_add_iff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] {a : WithTop.{u1} α} {b : WithTop.{u1} α} {c : WithTop.{u1} α} [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1))) (LT.lt.{u1} α _inst_2)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1))) (LT.lt.{u1} α _inst_2)], (Ne.{succ u1} (WithTop.{u1} α) a (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) -> (Iff (LT.lt.{u1} (WithTop.{u1} α) (WithTop.hasLt.{u1} α _inst_2) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) b a) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) c a)) (LT.lt.{u1} (WithTop.{u1} α) (WithTop.hasLt.{u1} α _inst_2) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] {a : WithTop.{u1} α} {b : WithTop.{u1} α} {c : WithTop.{u1} α} [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2770 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2772 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2770 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2772)) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2785 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2787 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2785 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2787)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2807 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2809 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2807 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2809)) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2822 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2824 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2822 x._@.Mathlib.Algebra.Order.Monoid.WithTop._hyg.2824)], (Ne.{succ u1} (WithTop.{u1} α) a (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))) -> (Iff (LT.lt.{u1} (WithTop.{u1} α) (WithTop.lt.{u1} α _inst_2) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) b a) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) c a)) (LT.lt.{u1} (WithTop.{u1} α) (WithTop.lt.{u1} α _inst_2) b c))
Case conversion may be inaccurate. Consider using '#align with_top.add_lt_add_iff_right WithTop.add_lt_add_iff_rightₓ'. -/
protected theorem add_lt_add_iff_right [LT α] [CovariantClass α α (swap (· + ·)) (· < ·)]
    [ContravariantClass α α (swap (· + ·)) (· < ·)] (ha : a ≠ ⊤) : b + a < c + a ↔ b < c :=
  ⟨lt_of_add_lt_add_right, WithTop.add_lt_add_right ha⟩
#align with_top.add_lt_add_iff_right WithTop.add_lt_add_iff_right

#print WithTop.add_lt_add_of_le_of_lt /-
protected theorem add_lt_add_of_le_of_lt [Preorder α] [CovariantClass α α (· + ·) (· < ·)]
    [CovariantClass α α (swap (· + ·)) (· ≤ ·)] (ha : a ≠ ⊤) (hab : a ≤ b) (hcd : c < d) :
    a + c < b + d :=
  (WithTop.add_lt_add_left ha hcd).trans_le <| add_le_add_right hab _
#align with_top.add_lt_add_of_le_of_lt WithTop.add_lt_add_of_le_of_lt
-/

#print WithTop.add_lt_add_of_lt_of_le /-
protected theorem add_lt_add_of_lt_of_le [Preorder α] [CovariantClass α α (· + ·) (· ≤ ·)]
    [CovariantClass α α (swap (· + ·)) (· < ·)] (hc : c ≠ ⊤) (hab : a < b) (hcd : c ≤ d) :
    a + c < b + d :=
  (WithTop.add_lt_add_right hc hab).trans_le <| add_le_add_left hcd _
#align with_top.add_lt_add_of_lt_of_le WithTop.add_lt_add_of_lt_of_le
-/

/- warning: with_top.map_add -> WithTop.map_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Add.{u1} α] {F : Type.{u3}} [_inst_2 : Add.{u2} β] [_inst_3 : AddHomClass.{u3, u1, u2} F α β _inst_1 _inst_2] (f : F) (a : WithTop.{u1} α) (b : WithTop.{u1} α), Eq.{succ u2} (WithTop.{u2} β) (WithTop.map.{u1, u2} α β (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F α (fun (_x : α) => β) (AddHomClass.toFunLike.{u3, u1, u2} F α β _inst_1 _inst_2 _inst_3)) f) (HAdd.hAdd.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHAdd.{u1} (WithTop.{u1} α) (WithTop.add.{u1} α _inst_1)) a b)) (HAdd.hAdd.{u2, u2, u2} (WithTop.{u2} β) (WithTop.{u2} β) (WithTop.{u2} β) (instHAdd.{u2} (WithTop.{u2} β) (WithTop.add.{u2} β _inst_2)) (WithTop.map.{u1, u2} α β (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F α (fun (_x : α) => β) (AddHomClass.toFunLike.{u3, u1, u2} F α β _inst_1 _inst_2 _inst_3)) f) a) (WithTop.map.{u1, u2} α β (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F α (fun (_x : α) => β) (AddHomClass.toFunLike.{u3, u1, u2} F α β _inst_1 _inst_2 _inst_3)) f) b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Add.{u2} α] {F : Type.{u1}} [_inst_2 : Add.{u3} β] [_inst_3 : AddHomClass.{u1, u2, u3} F α β _inst_1 _inst_2] (f : F) (a : WithTop.{u2} α) (b : WithTop.{u2} α), Eq.{succ u3} (WithTop.{u3} β) (WithTop.map.{u2, u3} α β (FunLike.coe.{succ u1, succ u2, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => β) _x) (AddHomClass.toFunLike.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3) f) (HAdd.hAdd.{u2, u2, u2} (WithTop.{u2} α) (WithTop.{u2} α) (WithTop.{u2} α) (instHAdd.{u2} (WithTop.{u2} α) (WithTop.add.{u2} α _inst_1)) a b)) (HAdd.hAdd.{u3, u3, u3} (WithTop.{u3} β) (WithTop.{u3} β) (WithTop.{u3} β) (instHAdd.{u3} (WithTop.{u3} β) (WithTop.add.{u3} β _inst_2)) (WithTop.map.{u2, u3} α β (FunLike.coe.{succ u1, succ u2, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => β) _x) (AddHomClass.toFunLike.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3) f) a) (WithTop.map.{u2, u3} α β (FunLike.coe.{succ u1, succ u2, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => β) _x) (AddHomClass.toFunLike.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3) f) b))
Case conversion may be inaccurate. Consider using '#align with_top.map_add WithTop.map_addₓ'. -/
--  There is no `with_top.map_mul_of_mul_hom`, since `with_top` does not have a multiplication.
@[simp]
protected theorem map_add {F} [Add β] [AddHomClass F α β] (f : F) (a b : WithTop α) :
    (a + b).map f = a.map f + b.map f :=
  by
  induction a using WithTop.recTopCoe
  · exact (top_add _).symm
  · induction b using WithTop.recTopCoe
    · exact (add_top _).symm
    · rw [map_coe, map_coe, ← coe_add, ← coe_add, ← map_add]
      rfl
#align with_top.map_add WithTop.map_add

end Add

instance [AddSemigroup α] : AddSemigroup (WithTop α) :=
  { WithTop.add with add_assoc := fun _ _ _ => Option.map₂_assoc add_assoc }

instance [AddCommSemigroup α] : AddCommSemigroup (WithTop α) :=
  { WithTop.addSemigroup with add_comm := fun _ _ => Option.map₂_comm add_comm }

instance [AddZeroClass α] : AddZeroClass (WithTop α) :=
  { WithTop.hasZero,
    WithTop.add with
    zero_add := Option.map₂_left_identity zero_add
    add_zero := Option.map₂_right_identity add_zero }

instance [AddMonoid α] : AddMonoid (WithTop α) :=
  { WithTop.addZeroClass, WithTop.hasZero, WithTop.addSemigroup with }

instance [AddCommMonoid α] : AddCommMonoid (WithTop α) :=
  { WithTop.addMonoid, WithTop.addCommSemigroup with }

instance [AddMonoidWithOne α] : AddMonoidWithOne (WithTop α) :=
  { WithTop.one,
    WithTop.addMonoid with
    natCast := fun n => ↑(n : α)
    nat_cast_zero := by rw [Nat.cast_zero, WithTop.coe_zero]
    nat_cast_succ := fun n => by rw [Nat.cast_add_one, WithTop.coe_add, WithTop.coe_one] }

instance [AddCommMonoidWithOne α] : AddCommMonoidWithOne (WithTop α) :=
  { WithTop.addMonoidWithOne, WithTop.addCommMonoid with }

instance [OrderedAddCommMonoid α] : OrderedAddCommMonoid (WithTop α) :=
  { WithTop.partialOrder, WithTop.addCommMonoid with
    add_le_add_left := by
      rintro a b h (_ | c); · simp [none_eq_top]
      rcases b with (_ | b); · simp [none_eq_top]
      rcases le_coe_iff.1 h with ⟨a, rfl, h⟩
      simp only [some_eq_coe, ← coe_add, coe_le_coe] at h⊢
      exact add_le_add_left h c }

instance [LinearOrderedAddCommMonoid α] : LinearOrderedAddCommMonoidWithTop (WithTop α) :=
  { WithTop.orderTop, WithTop.linearOrder, WithTop.orderedAddCommMonoid, Option.nontrivial with
    top_add' := WithTop.top_add }

instance [LE α] [Add α] [ExistsAddOfLE α] : ExistsAddOfLE (WithTop α) :=
  ⟨fun a b =>
    match a, b with
    | ⊤, ⊤ => by simp
    | (a : α), ⊤ => fun _ => ⟨⊤, rfl⟩
    | (a : α), (b : α) => fun h =>
      by
      obtain ⟨c, rfl⟩ := exists_add_of_le (WithTop.coe_le_coe.1 h)
      exact ⟨c, rfl⟩
    | ⊤, (b : α) => fun h => (not_top_le_coe _ h).elim⟩

instance [CanonicallyOrderedAddMonoid α] : CanonicallyOrderedAddMonoid (WithTop α) :=
  { WithTop.orderBot, WithTop.orderedAddCommMonoid, WithTop.existsAddOfLE with
    le_self_add := fun a b =>
      match a, b with
      | ⊤, ⊤ => le_rfl
      | (a : α), ⊤ => le_top
      | (a : α), (b : α) => WithTop.coe_le_coe.2 le_self_add
      | ⊤, (b : α) => le_rfl }

instance [CanonicallyLinearOrderedAddMonoid α] : CanonicallyLinearOrderedAddMonoid (WithTop α) :=
  { WithTop.canonicallyOrderedAddMonoid, WithTop.linearOrder with }

#print WithTop.coe_nat /-
@[simp, norm_cast]
theorem coe_nat [AddMonoidWithOne α] (n : ℕ) : ((n : α) : WithTop α) = n :=
  rfl
#align with_top.coe_nat WithTop.coe_nat
-/

#print WithTop.nat_ne_top /-
@[simp]
theorem nat_ne_top [AddMonoidWithOne α] (n : ℕ) : (n : WithTop α) ≠ ⊤ :=
  coe_ne_top
#align with_top.nat_ne_top WithTop.nat_ne_top
-/

#print WithTop.top_ne_nat /-
@[simp]
theorem top_ne_nat [AddMonoidWithOne α] (n : ℕ) : (⊤ : WithTop α) ≠ n :=
  top_ne_coe
#align with_top.top_ne_nat WithTop.top_ne_nat
-/

#print WithTop.addHom /-
/-- Coercion from `α` to `with_top α` as an `add_monoid_hom`. -/
def addHom [AddMonoid α] : α →+ WithTop α :=
  ⟨coe, rfl, fun _ _ => rfl⟩
#align with_top.coe_add_hom WithTop.addHom
-/

@[simp]
theorem coe_addHom [AddMonoid α] : ⇑(addHom : α →+ WithTop α) = coe :=
  rfl
#align with_top.coe_coe_add_hom WithTop.coe_addHom

/- warning: with_top.zero_lt_top -> WithTop.zero_lt_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedAddCommMonoid.{u1} α], LT.lt.{u1} (WithTop.{u1} α) (Preorder.toLT.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α _inst_1)))) (OfNat.ofNat.{u1} (WithTop.{u1} α) 0 (OfNat.mk.{u1} (WithTop.{u1} α) 0 (Zero.zero.{u1} (WithTop.{u1} α) (WithTop.hasZero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α _inst_1)))))))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedAddCommMonoid.{u1} α], LT.lt.{u1} (WithTop.{u1} α) (Preorder.toLT.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α _inst_1)))) (OfNat.ofNat.{u1} (WithTop.{u1} α) 0 (Zero.toOfNat0.{u1} (WithTop.{u1} α) (WithTop.zero.{u1} α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α _inst_1)))))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))
Case conversion may be inaccurate. Consider using '#align with_top.zero_lt_top WithTop.zero_lt_topₓ'. -/
@[simp]
theorem zero_lt_top [OrderedAddCommMonoid α] : (0 : WithTop α) < ⊤ :=
  coe_lt_top 0
#align with_top.zero_lt_top WithTop.zero_lt_top

/- warning: with_top.zero_lt_coe -> WithTop.zero_lt_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedAddCommMonoid.{u1} α] (a : α), Iff (LT.lt.{u1} (WithTop.{u1} α) (Preorder.toLT.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α _inst_1)))) (OfNat.ofNat.{u1} (WithTop.{u1} α) 0 (OfNat.mk.{u1} (WithTop.{u1} α) 0 (Zero.zero.{u1} (WithTop.{u1} α) (WithTop.hasZero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α _inst_1)))))))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) a)) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α _inst_1))))))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedAddCommMonoid.{u1} α] (a : α), Iff (LT.lt.{u1} (WithTop.{u1} α) (Preorder.toLT.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α _inst_1)))) (OfNat.ofNat.{u1} (WithTop.{u1} α) 0 (Zero.toOfNat0.{u1} (WithTop.{u1} α) (WithTop.zero.{u1} α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α _inst_1)))))) (WithTop.some.{u1} α a)) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α _inst_1))))) a)
Case conversion may be inaccurate. Consider using '#align with_top.zero_lt_coe WithTop.zero_lt_coeₓ'. -/
@[simp, norm_cast]
theorem zero_lt_coe [OrderedAddCommMonoid α] (a : α) : (0 : WithTop α) < a ↔ 0 < a :=
  coe_lt_coe
#align with_top.zero_lt_coe WithTop.zero_lt_coe

#print OneHom.withTopMap /-
/-- A version of `with_top.map` for `one_hom`s. -/
@[to_additive "A version of `with_top.map` for `zero_hom`s",
  simps (config := { fullyApplied := false })]
protected def OneHom.withTopMap {M N : Type _} [One M] [One N] (f : OneHom M N) :
    OneHom (WithTop M) (WithTop N) where
  toFun := WithTop.map f
  map_one' := by rw [WithTop.map_one, map_one, coe_one]
#align one_hom.with_top_map OneHom.withTopMap
#align zero_hom.with_top_map ZeroHom.withTopMap
-/

#print AddHom.withTopMap /-
/-- A version of `with_top.map` for `add_hom`s. -/
@[simps (config := { fullyApplied := false })]
protected def AddHom.withTopMap {M N : Type _} [Add M] [Add N] (f : AddHom M N) :
    AddHom (WithTop M) (WithTop N) where
  toFun := WithTop.map f
  map_add' := WithTop.map_add f
#align add_hom.with_top_map AddHom.withTopMap
-/

#print AddMonoidHom.withTopMap /-
/-- A version of `with_top.map` for `add_monoid_hom`s. -/
@[simps (config := { fullyApplied := false })]
protected def AddMonoidHom.withTopMap {M N : Type _} [AddZeroClass M] [AddZeroClass N]
    (f : M →+ N) : WithTop M →+ WithTop N :=
  { f.toZeroHom.with_top_map, f.toAddHom.with_top_map with toFun := WithTop.map f }
#align add_monoid_hom.with_top_map AddMonoidHom.withTopMap
-/

end WithTop

namespace WithBot

@[to_additive]
instance [One α] : One (WithBot α) :=
  WithTop.one

instance [Add α] : Add (WithBot α) :=
  WithTop.add

instance [AddSemigroup α] : AddSemigroup (WithBot α) :=
  WithTop.addSemigroup

instance [AddCommSemigroup α] : AddCommSemigroup (WithBot α) :=
  WithTop.addCommSemigroup

instance [AddZeroClass α] : AddZeroClass (WithBot α) :=
  WithTop.addZeroClass

instance [AddMonoid α] : AddMonoid (WithBot α) :=
  WithTop.addMonoid

instance [AddCommMonoid α] : AddCommMonoid (WithBot α) :=
  WithTop.addCommMonoid

instance [AddMonoidWithOne α] : AddMonoidWithOne (WithBot α) :=
  WithTop.addMonoidWithOne

instance [AddCommMonoidWithOne α] : AddCommMonoidWithOne (WithBot α) :=
  WithTop.addCommMonoidWithOne

instance [Zero α] [One α] [LE α] [ZeroLEOneClass α] : ZeroLEOneClass (WithBot α) :=
  ⟨some_le_some.2 zero_le_one⟩

#print WithBot.coe_one /-
-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
@[to_additive]
theorem coe_one [One α] : ((1 : α) : WithBot α) = 1 :=
  rfl
#align with_bot.coe_one WithBot.coe_one
#align with_bot.coe_zero WithBot.coe_zero
-/

#print WithBot.coe_eq_one /-
-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
@[to_additive]
theorem coe_eq_one [One α] {a : α} : (a : WithBot α) = 1 ↔ a = 1 :=
  WithTop.coe_eq_one
#align with_bot.coe_eq_one WithBot.coe_eq_one
#align with_bot.coe_eq_zero WithBot.coe_eq_zero
-/

/- warning: with_bot.one_lt_coe -> WithBot.one_lt_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : One.{u1} α] [_inst_2 : LT.{u1} α] {a : α}, Iff (LT.lt.{u1} (WithBot.{u1} α) (WithBot.hasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} (WithBot.{u1} α) 1 (OfNat.mk.{u1} (WithBot.{u1} α) 1 (One.one.{u1} (WithBot.{u1} α) (WithBot.hasOne.{u1} α _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) a)) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_1))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : One.{u1} α] [_inst_2 : LT.{u1} α] {a : α}, Iff (LT.lt.{u1} (WithBot.{u1} α) (WithBot.lt.{u1} α _inst_2) (OfNat.ofNat.{u1} (WithBot.{u1} α) 1 (One.toOfNat1.{u1} (WithBot.{u1} α) (WithBot.one.{u1} α _inst_1))) (WithBot.some.{u1} α a)) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α _inst_1)) a)
Case conversion may be inaccurate. Consider using '#align with_bot.one_lt_coe WithBot.one_lt_coeₓ'. -/
@[norm_cast, to_additive coe_pos]
theorem one_lt_coe [One α] [LT α] {a : α} : 1 < (a : WithBot α) ↔ 1 < a :=
  coe_lt_coe
#align with_bot.one_lt_coe WithBot.one_lt_coe
#align with_bot.coe_pos WithBot.coe_pos

/- warning: with_bot.coe_lt_one -> WithBot.coe_lt_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : One.{u1} α] [_inst_2 : LT.{u1} α] {a : α}, Iff (LT.lt.{u1} (WithBot.{u1} α) (WithBot.hasLt.{u1} α _inst_2) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) a) (OfNat.ofNat.{u1} (WithBot.{u1} α) 1 (OfNat.mk.{u1} (WithBot.{u1} α) 1 (One.one.{u1} (WithBot.{u1} α) (WithBot.hasOne.{u1} α _inst_1))))) (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : One.{u1} α] [_inst_2 : LT.{u1} α] {a : α}, Iff (LT.lt.{u1} (WithBot.{u1} α) (WithBot.lt.{u1} α _inst_2) (WithBot.some.{u1} α a) (OfNat.ofNat.{u1} (WithBot.{u1} α) 1 (One.toOfNat1.{u1} (WithBot.{u1} α) (WithBot.one.{u1} α _inst_1)))) (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align with_bot.coe_lt_one WithBot.coe_lt_oneₓ'. -/
@[norm_cast, to_additive coe_lt_zero]
theorem coe_lt_one [One α] [LT α] {a : α} : (a : WithBot α) < 1 ↔ a < 1 :=
  coe_lt_coe
#align with_bot.coe_lt_one WithBot.coe_lt_one
#align with_bot.coe_lt_zero WithBot.coe_lt_zero

/- warning: with_bot.map_one -> WithBot.map_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : One.{u1} α] (f : α -> β), Eq.{succ u2} (WithBot.{u2} β) (WithBot.map.{u1, u2} α β f (OfNat.ofNat.{u1} (WithBot.{u1} α) 1 (OfNat.mk.{u1} (WithBot.{u1} α) 1 (One.one.{u1} (WithBot.{u1} α) (WithBot.hasOne.{u1} α _inst_1))))) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) β (WithBot.{u2} β) (HasLiftT.mk.{succ u2, succ u2} β (WithBot.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} β (WithBot.{u2} β) (WithBot.hasCoeT.{u2} β))) (f (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : One.{u2} α] (f : α -> β), Eq.{succ u1} (WithBot.{u1} β) (WithBot.map.{u2, u1} α β f (OfNat.ofNat.{u2} (WithBot.{u2} α) 1 (One.toOfNat1.{u2} (WithBot.{u2} α) (WithBot.one.{u2} α _inst_1)))) (WithBot.some.{u1} β (f (OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align with_bot.map_one WithBot.map_oneₓ'. -/
@[to_additive]
protected theorem map_one {β} [One α] (f : α → β) : (1 : WithBot α).map f = (f 1 : WithBot β) :=
  rfl
#align with_bot.map_one WithBot.map_one
#align with_bot.map_zero WithBot.map_zero

#print WithBot.coe_nat /-
@[norm_cast]
theorem coe_nat [AddMonoidWithOne α] (n : ℕ) : ((n : α) : WithBot α) = n :=
  rfl
#align with_bot.coe_nat WithBot.coe_nat
-/

#print WithBot.nat_ne_bot /-
@[simp]
theorem nat_ne_bot [AddMonoidWithOne α] (n : ℕ) : (n : WithBot α) ≠ ⊥ :=
  coe_ne_bot
#align with_bot.nat_ne_bot WithBot.nat_ne_bot
-/

#print WithBot.bot_ne_nat /-
@[simp]
theorem bot_ne_nat [AddMonoidWithOne α] (n : ℕ) : (⊥ : WithBot α) ≠ n :=
  bot_ne_coe
#align with_bot.bot_ne_nat WithBot.bot_ne_nat
-/

section Add

variable [Add α] {a b c d : WithBot α} {x y : α}

#print WithBot.coe_add /-
-- `norm_cast` proves those lemmas, because `with_top`/`with_bot` are reducible
theorem coe_add (a b : α) : ((a + b : α) : WithBot α) = a + b :=
  rfl
#align with_bot.coe_add WithBot.coe_add
-/

#print WithBot.coe_bit0 /-
theorem coe_bit0 : ((bit0 x : α) : WithBot α) = bit0 x :=
  rfl
#align with_bot.coe_bit0 WithBot.coe_bit0
-/

#print WithBot.coe_bit1 /-
theorem coe_bit1 [One α] {a : α} : ((bit1 a : α) : WithBot α) = bit1 a :=
  rfl
#align with_bot.coe_bit1 WithBot.coe_bit1
-/

#print WithBot.bot_add /-
@[simp]
theorem bot_add (a : WithBot α) : ⊥ + a = ⊥ :=
  rfl
#align with_bot.bot_add WithBot.bot_add
-/

#print WithBot.add_bot /-
@[simp]
theorem add_bot (a : WithBot α) : a + ⊥ = ⊥ := by cases a <;> rfl
#align with_bot.add_bot WithBot.add_bot
-/

#print WithBot.add_eq_bot /-
@[simp]
theorem add_eq_bot : a + b = ⊥ ↔ a = ⊥ ∨ b = ⊥ :=
  WithTop.add_eq_top
#align with_bot.add_eq_bot WithBot.add_eq_bot
-/

#print WithBot.add_ne_bot /-
theorem add_ne_bot : a + b ≠ ⊥ ↔ a ≠ ⊥ ∧ b ≠ ⊥ :=
  WithTop.add_ne_top
#align with_bot.add_ne_bot WithBot.add_ne_bot
-/

#print WithBot.bot_lt_add /-
theorem bot_lt_add [PartialOrder α] {a b : WithBot α} : ⊥ < a + b ↔ ⊥ < a ∧ ⊥ < b :=
  @WithTop.add_lt_top αᵒᵈ _ _ _ _
#align with_bot.bot_lt_add WithBot.bot_lt_add
-/

#print WithBot.add_eq_coe /-
theorem add_eq_coe : a + b = x ↔ ∃ a' b' : α, ↑a' = a ∧ ↑b' = b ∧ a' + b' = x :=
  WithTop.add_eq_coe
#align with_bot.add_eq_coe WithBot.add_eq_coe
-/

#print WithBot.add_coe_eq_bot_iff /-
@[simp]
theorem add_coe_eq_bot_iff : a + y = ⊥ ↔ a = ⊥ :=
  WithTop.add_coe_eq_top_iff
#align with_bot.add_coe_eq_bot_iff WithBot.add_coe_eq_bot_iff
-/

#print WithBot.coe_add_eq_bot_iff /-
@[simp]
theorem coe_add_eq_bot_iff : ↑x + b = ⊥ ↔ b = ⊥ :=
  WithTop.coe_add_eq_top_iff
#align with_bot.coe_add_eq_bot_iff WithBot.coe_add_eq_bot_iff
-/

/- warning: with_bot.map_add -> WithBot.map_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Add.{u1} α] {F : Type.{u3}} [_inst_2 : Add.{u2} β] [_inst_3 : AddHomClass.{u3, u1, u2} F α β _inst_1 _inst_2] (f : F) (a : WithBot.{u1} α) (b : WithBot.{u1} α), Eq.{succ u2} (WithBot.{u2} β) (WithBot.map.{u1, u2} α β (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F α (fun (_x : α) => β) (AddHomClass.toFunLike.{u3, u1, u2} F α β _inst_1 _inst_2 _inst_3)) f) (HAdd.hAdd.{u1, u1, u1} (WithBot.{u1} α) (WithBot.{u1} α) (WithBot.{u1} α) (instHAdd.{u1} (WithBot.{u1} α) (WithBot.hasAdd.{u1} α _inst_1)) a b)) (HAdd.hAdd.{u2, u2, u2} (WithBot.{u2} β) (WithBot.{u2} β) (WithBot.{u2} β) (instHAdd.{u2} (WithBot.{u2} β) (WithBot.hasAdd.{u2} β _inst_2)) (WithBot.map.{u1, u2} α β (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F α (fun (_x : α) => β) (AddHomClass.toFunLike.{u3, u1, u2} F α β _inst_1 _inst_2 _inst_3)) f) a) (WithBot.map.{u1, u2} α β (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F α (fun (_x : α) => β) (AddHomClass.toFunLike.{u3, u1, u2} F α β _inst_1 _inst_2 _inst_3)) f) b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Add.{u2} α] {F : Type.{u1}} [_inst_2 : Add.{u3} β] [_inst_3 : AddHomClass.{u1, u2, u3} F α β _inst_1 _inst_2] (f : F) (a : WithBot.{u2} α) (b : WithBot.{u2} α), Eq.{succ u3} (WithBot.{u3} β) (WithBot.map.{u2, u3} α β (FunLike.coe.{succ u1, succ u2, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => β) _x) (AddHomClass.toFunLike.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3) f) (HAdd.hAdd.{u2, u2, u2} (WithBot.{u2} α) (WithBot.{u2} α) (WithBot.{u2} α) (instHAdd.{u2} (WithBot.{u2} α) (WithBot.add.{u2} α _inst_1)) a b)) (HAdd.hAdd.{u3, u3, u3} (WithBot.{u3} β) (WithBot.{u3} β) (WithBot.{u3} β) (instHAdd.{u3} (WithBot.{u3} β) (WithBot.add.{u3} β _inst_2)) (WithBot.map.{u2, u3} α β (FunLike.coe.{succ u1, succ u2, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => β) _x) (AddHomClass.toFunLike.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3) f) a) (WithBot.map.{u2, u3} α β (FunLike.coe.{succ u1, succ u2, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => β) _x) (AddHomClass.toFunLike.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3) f) b))
Case conversion may be inaccurate. Consider using '#align with_bot.map_add WithBot.map_addₓ'. -/
--  There is no `with_bot.map_mul_of_mul_hom`, since `with_bot` does not have a multiplication.
@[simp]
protected theorem map_add {F} [Add β] [AddHomClass F α β] (f : F) (a b : WithBot α) :
    (a + b).map f = a.map f + b.map f :=
  WithTop.map_add f a b
#align with_bot.map_add WithBot.map_add

#print OneHom.withBotMap /-
/-- A version of `with_bot.map` for `one_hom`s. -/
@[to_additive "A version of `with_bot.map` for `zero_hom`s",
  simps (config := { fullyApplied := false })]
protected def OneHom.withBotMap {M N : Type _} [One M] [One N] (f : OneHom M N) :
    OneHom (WithBot M) (WithBot N) where
  toFun := WithBot.map f
  map_one' := by rw [WithBot.map_one, map_one, coe_one]
#align one_hom.with_bot_map OneHom.withBotMap
#align zero_hom.with_bot_map ZeroHom.withBotMap
-/

#print AddHom.withBotMap /-
/-- A version of `with_bot.map` for `add_hom`s. -/
@[simps (config := { fullyApplied := false })]
protected def AddHom.withBotMap {M N : Type _} [Add M] [Add N] (f : AddHom M N) :
    AddHom (WithBot M) (WithBot N) where
  toFun := WithBot.map f
  map_add' := WithBot.map_add f
#align add_hom.with_bot_map AddHom.withBotMap
-/

#print AddMonoidHom.withBotMap /-
/-- A version of `with_bot.map` for `add_monoid_hom`s. -/
@[simps (config := { fullyApplied := false })]
protected def AddMonoidHom.withBotMap {M N : Type _} [AddZeroClass M] [AddZeroClass N]
    (f : M →+ N) : WithBot M →+ WithBot N :=
  { f.toZeroHom.with_bot_map, f.toAddHom.with_bot_map with toFun := WithBot.map f }
#align add_monoid_hom.with_bot_map AddMonoidHom.withBotMap
-/

variable [Preorder α]

#print WithBot.covariantClass_add_le /-
instance covariantClass_add_le [CovariantClass α α (· + ·) (· ≤ ·)] :
    CovariantClass (WithBot α) (WithBot α) (· + ·) (· ≤ ·) :=
  @OrderDual.covariantClass_add_le (WithTop αᵒᵈ) _ _ _
#align with_bot.covariant_class_add_le WithBot.covariantClass_add_le
-/

#print WithBot.covariantClass_swap_add_le /-
instance covariantClass_swap_add_le [CovariantClass α α (swap (· + ·)) (· ≤ ·)] :
    CovariantClass (WithBot α) (WithBot α) (swap (· + ·)) (· ≤ ·) :=
  @OrderDual.covariantClass_swap_add_le (WithTop αᵒᵈ) _ _ _
#align with_bot.covariant_class_swap_add_le WithBot.covariantClass_swap_add_le
-/

#print WithBot.contravariantClass_add_lt /-
instance contravariantClass_add_lt [ContravariantClass α α (· + ·) (· < ·)] :
    ContravariantClass (WithBot α) (WithBot α) (· + ·) (· < ·) :=
  @OrderDual.contravariantClass_add_lt (WithTop αᵒᵈ) _ _ _
#align with_bot.contravariant_class_add_lt WithBot.contravariantClass_add_lt
-/

#print WithBot.contravariantClass_swap_add_lt /-
instance contravariantClass_swap_add_lt [ContravariantClass α α (swap (· + ·)) (· < ·)] :
    ContravariantClass (WithBot α) (WithBot α) (swap (· + ·)) (· < ·) :=
  @OrderDual.contravariantClass_swap_add_lt (WithTop αᵒᵈ) _ _ _
#align with_bot.contravariant_class_swap_add_lt WithBot.contravariantClass_swap_add_lt
-/

#print WithBot.le_of_add_le_add_left /-
protected theorem le_of_add_le_add_left [ContravariantClass α α (· + ·) (· ≤ ·)] (ha : a ≠ ⊥)
    (h : a + b ≤ a + c) : b ≤ c :=
  @WithTop.le_of_add_le_add_left αᵒᵈ _ _ _ _ _ _ ha h
#align with_bot.le_of_add_le_add_left WithBot.le_of_add_le_add_left
-/

#print WithBot.le_of_add_le_add_right /-
protected theorem le_of_add_le_add_right [ContravariantClass α α (swap (· + ·)) (· ≤ ·)]
    (ha : a ≠ ⊥) (h : b + a ≤ c + a) : b ≤ c :=
  @WithTop.le_of_add_le_add_right αᵒᵈ _ _ _ _ _ _ ha h
#align with_bot.le_of_add_le_add_right WithBot.le_of_add_le_add_right
-/

#print WithBot.add_lt_add_left /-
protected theorem add_lt_add_left [CovariantClass α α (· + ·) (· < ·)] (ha : a ≠ ⊥) (h : b < c) :
    a + b < a + c :=
  @WithTop.add_lt_add_left αᵒᵈ _ _ _ _ _ _ ha h
#align with_bot.add_lt_add_left WithBot.add_lt_add_left
-/

#print WithBot.add_lt_add_right /-
protected theorem add_lt_add_right [CovariantClass α α (swap (· + ·)) (· < ·)] (ha : a ≠ ⊥)
    (h : b < c) : b + a < c + a :=
  @WithTop.add_lt_add_right αᵒᵈ _ _ _ _ _ _ ha h
#align with_bot.add_lt_add_right WithBot.add_lt_add_right
-/

#print WithBot.add_le_add_iff_left /-
protected theorem add_le_add_iff_left [CovariantClass α α (· + ·) (· ≤ ·)]
    [ContravariantClass α α (· + ·) (· ≤ ·)] (ha : a ≠ ⊥) : a + b ≤ a + c ↔ b ≤ c :=
  ⟨WithBot.le_of_add_le_add_left ha, fun h => add_le_add_left h a⟩
#align with_bot.add_le_add_iff_left WithBot.add_le_add_iff_left
-/

#print WithBot.add_le_add_iff_right /-
protected theorem add_le_add_iff_right [CovariantClass α α (swap (· + ·)) (· ≤ ·)]
    [ContravariantClass α α (swap (· + ·)) (· ≤ ·)] (ha : a ≠ ⊥) : b + a ≤ c + a ↔ b ≤ c :=
  ⟨WithBot.le_of_add_le_add_right ha, fun h => add_le_add_right h a⟩
#align with_bot.add_le_add_iff_right WithBot.add_le_add_iff_right
-/

#print WithBot.add_lt_add_iff_left /-
protected theorem add_lt_add_iff_left [CovariantClass α α (· + ·) (· < ·)]
    [ContravariantClass α α (· + ·) (· < ·)] (ha : a ≠ ⊥) : a + b < a + c ↔ b < c :=
  ⟨lt_of_add_lt_add_left, WithBot.add_lt_add_left ha⟩
#align with_bot.add_lt_add_iff_left WithBot.add_lt_add_iff_left
-/

#print WithBot.add_lt_add_iff_right /-
protected theorem add_lt_add_iff_right [CovariantClass α α (swap (· + ·)) (· < ·)]
    [ContravariantClass α α (swap (· + ·)) (· < ·)] (ha : a ≠ ⊥) : b + a < c + a ↔ b < c :=
  ⟨lt_of_add_lt_add_right, WithBot.add_lt_add_right ha⟩
#align with_bot.add_lt_add_iff_right WithBot.add_lt_add_iff_right
-/

#print WithBot.add_lt_add_of_le_of_lt /-
protected theorem add_lt_add_of_le_of_lt [CovariantClass α α (· + ·) (· < ·)]
    [CovariantClass α α (swap (· + ·)) (· ≤ ·)] (hb : b ≠ ⊥) (hab : a ≤ b) (hcd : c < d) :
    a + c < b + d :=
  @WithTop.add_lt_add_of_le_of_lt αᵒᵈ _ _ _ _ _ _ _ _ hb hab hcd
#align with_bot.add_lt_add_of_le_of_lt WithBot.add_lt_add_of_le_of_lt
-/

#print WithBot.add_lt_add_of_lt_of_le /-
protected theorem add_lt_add_of_lt_of_le [CovariantClass α α (· + ·) (· ≤ ·)]
    [CovariantClass α α (swap (· + ·)) (· < ·)] (hd : d ≠ ⊥) (hab : a < b) (hcd : c ≤ d) :
    a + c < b + d :=
  @WithTop.add_lt_add_of_lt_of_le αᵒᵈ _ _ _ _ _ _ _ _ hd hab hcd
#align with_bot.add_lt_add_of_lt_of_le WithBot.add_lt_add_of_lt_of_le
-/

end Add

instance [OrderedAddCommMonoid α] : OrderedAddCommMonoid (WithBot α) :=
  { WithBot.partialOrder, WithBot.addCommMonoid with
    add_le_add_left := fun a b h c => add_le_add_left h c }

instance [LinearOrderedAddCommMonoid α] : LinearOrderedAddCommMonoid (WithBot α) :=
  { WithBot.linearOrder, WithBot.orderedAddCommMonoid with }

end WithBot

