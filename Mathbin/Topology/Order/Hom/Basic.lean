/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module topology.order.hom.basic
! leanprover-community/mathlib commit d101e93197bb5f6ea89bd7ba386b7f7dff1f3903
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Hom.Basic
import Mathbin.Topology.ContinuousFunction.Basic

/-!
# Continuous order homomorphisms

This file defines continuous order homomorphisms, that is maps which are both continuous and
monotone. They are also called Priestley homomorphisms because they are the morphisms of the
category of Priestley spaces.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `continuous_order_hom`: Continuous monotone functions, aka Priestley homomorphisms.

## Typeclasses

* `continuous_order_hom_class`
-/


open Function

variable {F α β γ δ : Type _}

#print ContinuousOrderHom /-
/-- The type of continuous monotone maps from `α` to `β`, aka Priestley homomorphisms. -/
structure ContinuousOrderHom (α β : Type _) [Preorder α] [Preorder β] [TopologicalSpace α]
  [TopologicalSpace β] extends OrderHom α β where
  continuous_toFun : Continuous to_fun
#align continuous_order_hom ContinuousOrderHom
-/

-- mathport name: «expr →Co »
infixr:25 " →Co " => ContinuousOrderHom

section

#print ContinuousOrderHomClass /-
/-- `continuous_order_hom_class F α β` states that `F` is a type of continuous monotone maps.

You should extend this class when you extend `continuous_order_hom`. -/
class ContinuousOrderHomClass (F : Type _) (α β : outParam <| Type _) [Preorder α] [Preorder β]
  [TopologicalSpace α] [TopologicalSpace β] extends
  RelHomClass F ((· ≤ ·) : α → α → Prop) ((· ≤ ·) : β → β → Prop) where
  map_continuous (f : F) : Continuous f
#align continuous_order_hom_class ContinuousOrderHomClass
-/

end

#print ContinuousOrderHomClass.toContinuousMapClass /-
-- See note [lower instance priority]
instance (priority := 100) ContinuousOrderHomClass.toContinuousMapClass [Preorder α] [Preorder β]
    [TopologicalSpace α] [TopologicalSpace β] [ContinuousOrderHomClass F α β] :
    ContinuousMapClass F α β :=
  { ‹ContinuousOrderHomClass F α β› with }
#align continuous_order_hom_class.to_continuous_map_class ContinuousOrderHomClass.toContinuousMapClass
-/

instance [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]
    [ContinuousOrderHomClass F α β] : CoeTC F (α →Co β) :=
  ⟨fun f =>
    { toFun := f
      monotone' := OrderHomClass.mono f
      continuous_toFun := map_continuous f }⟩

/-! ### Top homomorphisms -/


namespace ContinuousOrderHom

variable [TopologicalSpace α] [Preorder α] [TopologicalSpace β]

section Preorder

variable [Preorder β] [TopologicalSpace γ] [Preorder γ] [TopologicalSpace δ] [Preorder δ]

#print ContinuousOrderHom.toContinuousMap /-
/-- Reinterpret a `continuous_order_hom` as a `continuous_map`. -/
def toContinuousMap (f : α →Co β) : C(α, β) :=
  { f with }
#align continuous_order_hom.to_continuous_map ContinuousOrderHom.toContinuousMap
-/

instance : ContinuousOrderHomClass (α →Co β) α β
    where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
  map_rel f := f.monotone'
  map_continuous f := f.continuous_toFun

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (α →Co β) fun _ => α → β :=
  FunLike.hasCoeToFun

/- warning: continuous_order_hom.to_fun_eq_coe -> ContinuousOrderHom.toFun_eq_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : TopologicalSpace.{u2} β] [_inst_4 : Preorder.{u2} β] {f : ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3}, Eq.{max (succ u1) (succ u2)} (α -> β) (OrderHom.toFun.{u1, u2} α β _inst_2 _inst_4 (ContinuousOrderHom.toOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3 f)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) (fun (_x : ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) => α -> β) (ContinuousOrderHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : TopologicalSpace.{u1} β] [_inst_4 : Preorder.{u1} β] {f : ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3}, Eq.{max (succ u2) (succ u1)} (α -> β) (OrderHom.toFun.{u2, u1} α β _inst_2 _inst_4 (ContinuousOrderHom.toOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3 f)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3) α β _inst_1 _inst_3 (ContinuousOrderHomClass.toContinuousMapClass.{max u2 u1, u2, u1} (ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3) α β _inst_2 _inst_4 _inst_1 _inst_3 (ContinuousOrderHom.instContinuousOrderHomClassContinuousOrderHom.{u2, u1} α β _inst_1 _inst_2 _inst_3 _inst_4))) f)
Case conversion may be inaccurate. Consider using '#align continuous_order_hom.to_fun_eq_coe ContinuousOrderHom.toFun_eq_coeₓ'. -/
@[simp]
theorem toFun_eq_coe {f : α →Co β} : f.toFun = (f : α → β) :=
  rfl
#align continuous_order_hom.to_fun_eq_coe ContinuousOrderHom.toFun_eq_coe

/- warning: continuous_order_hom.ext -> ContinuousOrderHom.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : TopologicalSpace.{u2} β] [_inst_4 : Preorder.{u2} β] {f : ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3} {g : ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3}, (forall (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) (fun (_x : ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) => α -> β) (ContinuousOrderHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) (fun (_x : ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) => α -> β) (ContinuousOrderHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) g a)) -> (Eq.{max (succ u1) (succ u2)} (ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : TopologicalSpace.{u1} β] [_inst_4 : Preorder.{u1} β] {f : ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3} {g : ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3}, (forall (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3) α β _inst_1 _inst_3 (ContinuousOrderHomClass.toContinuousMapClass.{max u2 u1, u2, u1} (ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3) α β _inst_2 _inst_4 _inst_1 _inst_3 (ContinuousOrderHom.instContinuousOrderHomClassContinuousOrderHom.{u2, u1} α β _inst_1 _inst_2 _inst_3 _inst_4))) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3) α β _inst_1 _inst_3 (ContinuousOrderHomClass.toContinuousMapClass.{max u2 u1, u2, u1} (ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3) α β _inst_2 _inst_4 _inst_1 _inst_3 (ContinuousOrderHom.instContinuousOrderHomClassContinuousOrderHom.{u2, u1} α β _inst_1 _inst_2 _inst_3 _inst_4))) g a)) -> (Eq.{max (succ u2) (succ u1)} (ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3) f g)
Case conversion may be inaccurate. Consider using '#align continuous_order_hom.ext ContinuousOrderHom.extₓ'. -/
@[ext]
theorem ext {f g : α →Co β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align continuous_order_hom.ext ContinuousOrderHom.ext

/- warning: continuous_order_hom.copy -> ContinuousOrderHom.copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : TopologicalSpace.{u2} β] [_inst_4 : Preorder.{u2} β] (f : ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) (fun (_x : ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) => α -> β) (ContinuousOrderHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) f)) -> (ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : TopologicalSpace.{u2} β] [_inst_4 : Preorder.{u2} β] (f : ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) α β _inst_1 _inst_3 (ContinuousOrderHomClass.toContinuousMapClass.{max u1 u2, u1, u2} (ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) α β _inst_2 _inst_4 _inst_1 _inst_3 (ContinuousOrderHom.instContinuousOrderHomClassContinuousOrderHom.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4))) f)) -> (ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3)
Case conversion may be inaccurate. Consider using '#align continuous_order_hom.copy ContinuousOrderHom.copyₓ'. -/
/-- Copy of a `continuous_order_hom` with a new `continuous_map` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : α →Co β) (f' : α → β) (h : f' = f) : α →Co β :=
  ⟨f.toOrderHom.copy f' <| h, h.symm.subst f.continuous_toFun⟩
#align continuous_order_hom.copy ContinuousOrderHom.copy

/- warning: continuous_order_hom.coe_copy -> ContinuousOrderHom.coe_copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : TopologicalSpace.{u2} β] [_inst_4 : Preorder.{u2} β] (f : ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) (fun (_x : ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) => α -> β) (ContinuousOrderHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) f)), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) (fun (_x : ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) => α -> β) (ContinuousOrderHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) (ContinuousOrderHom.copy.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4 f f' h)) f'
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : TopologicalSpace.{u1} β] [_inst_4 : Preorder.{u1} β] (f : ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3) α β _inst_1 _inst_3 (ContinuousOrderHomClass.toContinuousMapClass.{max u2 u1, u2, u1} (ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3) α β _inst_2 _inst_4 _inst_1 _inst_3 (ContinuousOrderHom.instContinuousOrderHomClassContinuousOrderHom.{u2, u1} α β _inst_1 _inst_2 _inst_3 _inst_4))) f)), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3) α β _inst_1 _inst_3 (ContinuousOrderHomClass.toContinuousMapClass.{max u2 u1, u2, u1} (ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3) α β _inst_2 _inst_4 _inst_1 _inst_3 (ContinuousOrderHom.instContinuousOrderHomClassContinuousOrderHom.{u2, u1} α β _inst_1 _inst_2 _inst_3 _inst_4))) (ContinuousOrderHom.copy.{u2, u1} α β _inst_1 _inst_2 _inst_3 _inst_4 f f' h)) f'
Case conversion may be inaccurate. Consider using '#align continuous_order_hom.coe_copy ContinuousOrderHom.coe_copyₓ'. -/
@[simp]
theorem coe_copy (f : α →Co β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align continuous_order_hom.coe_copy ContinuousOrderHom.coe_copy

/- warning: continuous_order_hom.copy_eq -> ContinuousOrderHom.copy_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : TopologicalSpace.{u2} β] [_inst_4 : Preorder.{u2} β] (f : ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) (fun (_x : ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) => α -> β) (ContinuousOrderHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) f)), Eq.{max (succ u1) (succ u2)} (ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) (ContinuousOrderHom.copy.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4 f f' h) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : TopologicalSpace.{u1} β] [_inst_4 : Preorder.{u1} β] (f : ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3) α β _inst_1 _inst_3 (ContinuousOrderHomClass.toContinuousMapClass.{max u2 u1, u2, u1} (ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3) α β _inst_2 _inst_4 _inst_1 _inst_3 (ContinuousOrderHom.instContinuousOrderHomClassContinuousOrderHom.{u2, u1} α β _inst_1 _inst_2 _inst_3 _inst_4))) f)), Eq.{max (succ u2) (succ u1)} (ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3) (ContinuousOrderHom.copy.{u2, u1} α β _inst_1 _inst_2 _inst_3 _inst_4 f f' h) f
Case conversion may be inaccurate. Consider using '#align continuous_order_hom.copy_eq ContinuousOrderHom.copy_eqₓ'. -/
theorem copy_eq (f : α →Co β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align continuous_order_hom.copy_eq ContinuousOrderHom.copy_eq

variable (α)

#print ContinuousOrderHom.id /-
/-- `id` as a `continuous_order_hom`. -/
protected def id : α →Co α :=
  ⟨OrderHom.id, continuous_id⟩
#align continuous_order_hom.id ContinuousOrderHom.id
-/

instance : Inhabited (α →Co α) :=
  ⟨ContinuousOrderHom.id _⟩

/- warning: continuous_order_hom.coe_id -> ContinuousOrderHom.coe_id is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α], Eq.{succ u1} (α -> α) (coeFn.{succ u1, succ u1} (ContinuousOrderHom.{u1, u1} α α _inst_2 _inst_2 _inst_1 _inst_1) (fun (_x : ContinuousOrderHom.{u1, u1} α α _inst_2 _inst_2 _inst_1 _inst_1) => α -> α) (ContinuousOrderHom.hasCoeToFun.{u1, u1} α α _inst_1 _inst_2 _inst_1 _inst_2) (ContinuousOrderHom.id.{u1} α _inst_1 _inst_2)) (id.{succ u1} α)
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α], Eq.{succ u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => α) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (ContinuousOrderHom.{u1, u1} α α _inst_2 _inst_2 _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => α) _x) (ContinuousMapClass.toFunLike.{u1, u1, u1} (ContinuousOrderHom.{u1, u1} α α _inst_2 _inst_2 _inst_1 _inst_1) α α _inst_1 _inst_1 (ContinuousOrderHomClass.toContinuousMapClass.{u1, u1, u1} (ContinuousOrderHom.{u1, u1} α α _inst_2 _inst_2 _inst_1 _inst_1) α α _inst_2 _inst_2 _inst_1 _inst_1 (ContinuousOrderHom.instContinuousOrderHomClassContinuousOrderHom.{u1, u1} α α _inst_1 _inst_2 _inst_1 _inst_2))) (ContinuousOrderHom.id.{u1} α _inst_1 _inst_2)) (id.{succ u1} α)
Case conversion may be inaccurate. Consider using '#align continuous_order_hom.coe_id ContinuousOrderHom.coe_idₓ'. -/
@[simp]
theorem coe_id : ⇑(ContinuousOrderHom.id α) = id :=
  rfl
#align continuous_order_hom.coe_id ContinuousOrderHom.coe_id

variable {α}

/- warning: continuous_order_hom.id_apply -> ContinuousOrderHom.id_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] (a : α), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (ContinuousOrderHom.{u1, u1} α α _inst_2 _inst_2 _inst_1 _inst_1) (fun (_x : ContinuousOrderHom.{u1, u1} α α _inst_2 _inst_2 _inst_1 _inst_1) => α -> α) (ContinuousOrderHom.hasCoeToFun.{u1, u1} α α _inst_1 _inst_2 _inst_1 _inst_2) (ContinuousOrderHom.id.{u1} α _inst_1 _inst_2) a) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (ContinuousOrderHom.{u1, u1} α α _inst_2 _inst_2 _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => α) _x) (ContinuousMapClass.toFunLike.{u1, u1, u1} (ContinuousOrderHom.{u1, u1} α α _inst_2 _inst_2 _inst_1 _inst_1) α α _inst_1 _inst_1 (ContinuousOrderHomClass.toContinuousMapClass.{u1, u1, u1} (ContinuousOrderHom.{u1, u1} α α _inst_2 _inst_2 _inst_1 _inst_1) α α _inst_2 _inst_2 _inst_1 _inst_1 (ContinuousOrderHom.instContinuousOrderHomClassContinuousOrderHom.{u1, u1} α α _inst_1 _inst_2 _inst_1 _inst_2))) (ContinuousOrderHom.id.{u1} α _inst_1 _inst_2) a) a
Case conversion may be inaccurate. Consider using '#align continuous_order_hom.id_apply ContinuousOrderHom.id_applyₓ'. -/
@[simp]
theorem id_apply (a : α) : ContinuousOrderHom.id α a = a :=
  rfl
#align continuous_order_hom.id_apply ContinuousOrderHom.id_apply

#print ContinuousOrderHom.comp /-
/-- Composition of `continuous_order_hom`s as a `continuous_order_hom`. -/
def comp (f : β →Co γ) (g : α →Co β) : ContinuousOrderHom α γ :=
  ⟨f.toOrderHom.comp g.toOrderHom, f.continuous_toFun.comp g.continuous_toFun⟩
#align continuous_order_hom.comp ContinuousOrderHom.comp
-/

/- warning: continuous_order_hom.coe_comp -> ContinuousOrderHom.coe_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : TopologicalSpace.{u2} β] [_inst_4 : Preorder.{u2} β] [_inst_5 : TopologicalSpace.{u3} γ] [_inst_6 : Preorder.{u3} γ] (f : ContinuousOrderHom.{u2, u3} β γ _inst_4 _inst_6 _inst_3 _inst_5) (g : ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3), Eq.{max (succ u1) (succ u3)} ((fun (_x : ContinuousOrderHom.{u1, u3} α γ _inst_2 _inst_6 _inst_1 _inst_5) => α -> γ) (ContinuousOrderHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 f g)) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (ContinuousOrderHom.{u1, u3} α γ _inst_2 _inst_6 _inst_1 _inst_5) (fun (_x : ContinuousOrderHom.{u1, u3} α γ _inst_2 _inst_6 _inst_1 _inst_5) => α -> γ) (ContinuousOrderHom.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_2 _inst_5 _inst_6) (ContinuousOrderHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 f g)) (Function.comp.{succ u1, succ u2, succ u3} α β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (ContinuousOrderHom.{u2, u3} β γ _inst_4 _inst_6 _inst_3 _inst_5) (fun (_x : ContinuousOrderHom.{u2, u3} β γ _inst_4 _inst_6 _inst_3 _inst_5) => β -> γ) (ContinuousOrderHom.hasCoeToFun.{u2, u3} β γ _inst_3 _inst_4 _inst_5 _inst_6) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) (fun (_x : ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) => α -> β) (ContinuousOrderHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : TopologicalSpace.{u3} β] [_inst_4 : Preorder.{u3} β] [_inst_5 : TopologicalSpace.{u2} γ] [_inst_6 : Preorder.{u2} γ] (f : ContinuousOrderHom.{u3, u2} β γ _inst_4 _inst_6 _inst_3 _inst_5) (g : ContinuousOrderHom.{u1, u3} α β _inst_2 _inst_4 _inst_1 _inst_3), Eq.{max (succ u1) (succ u2)} (forall (a : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => γ) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousOrderHom.{u1, u2} α γ _inst_2 _inst_6 _inst_1 _inst_5) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => γ) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousOrderHom.{u1, u2} α γ _inst_2 _inst_6 _inst_1 _inst_5) α γ _inst_1 _inst_5 (ContinuousOrderHomClass.toContinuousMapClass.{max u1 u2, u1, u2} (ContinuousOrderHom.{u1, u2} α γ _inst_2 _inst_6 _inst_1 _inst_5) α γ _inst_2 _inst_6 _inst_1 _inst_5 (ContinuousOrderHom.instContinuousOrderHomClassContinuousOrderHom.{u1, u2} α γ _inst_1 _inst_2 _inst_5 _inst_6))) (ContinuousOrderHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 f g)) (Function.comp.{succ u1, succ u3, succ u2} α β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (ContinuousOrderHom.{u3, u2} β γ _inst_4 _inst_6 _inst_3 _inst_5) β (fun (_x : β) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : β) => γ) _x) (ContinuousMapClass.toFunLike.{max u3 u2, u3, u2} (ContinuousOrderHom.{u3, u2} β γ _inst_4 _inst_6 _inst_3 _inst_5) β γ _inst_3 _inst_5 (ContinuousOrderHomClass.toContinuousMapClass.{max u3 u2, u3, u2} (ContinuousOrderHom.{u3, u2} β γ _inst_4 _inst_6 _inst_3 _inst_5) β γ _inst_4 _inst_6 _inst_3 _inst_5 (ContinuousOrderHom.instContinuousOrderHomClassContinuousOrderHom.{u3, u2} β γ _inst_3 _inst_4 _inst_5 _inst_6))) f) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (ContinuousOrderHom.{u1, u3} α β _inst_2 _inst_4 _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u3, u1, u3} (ContinuousOrderHom.{u1, u3} α β _inst_2 _inst_4 _inst_1 _inst_3) α β _inst_1 _inst_3 (ContinuousOrderHomClass.toContinuousMapClass.{max u1 u3, u1, u3} (ContinuousOrderHom.{u1, u3} α β _inst_2 _inst_4 _inst_1 _inst_3) α β _inst_2 _inst_4 _inst_1 _inst_3 (ContinuousOrderHom.instContinuousOrderHomClassContinuousOrderHom.{u1, u3} α β _inst_1 _inst_2 _inst_3 _inst_4))) g))
Case conversion may be inaccurate. Consider using '#align continuous_order_hom.coe_comp ContinuousOrderHom.coe_compₓ'. -/
@[simp]
theorem coe_comp (f : β →Co γ) (g : α →Co β) : (f.comp g : α → γ) = f ∘ g :=
  rfl
#align continuous_order_hom.coe_comp ContinuousOrderHom.coe_comp

/- warning: continuous_order_hom.comp_apply -> ContinuousOrderHom.comp_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : TopologicalSpace.{u2} β] [_inst_4 : Preorder.{u2} β] [_inst_5 : TopologicalSpace.{u3} γ] [_inst_6 : Preorder.{u3} γ] (f : ContinuousOrderHom.{u2, u3} β γ _inst_4 _inst_6 _inst_3 _inst_5) (g : ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) (a : α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (ContinuousOrderHom.{u1, u3} α γ _inst_2 _inst_6 _inst_1 _inst_5) (fun (_x : ContinuousOrderHom.{u1, u3} α γ _inst_2 _inst_6 _inst_1 _inst_5) => α -> γ) (ContinuousOrderHom.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_2 _inst_5 _inst_6) (ContinuousOrderHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 f g) a) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (ContinuousOrderHom.{u2, u3} β γ _inst_4 _inst_6 _inst_3 _inst_5) (fun (_x : ContinuousOrderHom.{u2, u3} β γ _inst_4 _inst_6 _inst_3 _inst_5) => β -> γ) (ContinuousOrderHom.hasCoeToFun.{u2, u3} β γ _inst_3 _inst_4 _inst_5 _inst_6) f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) (fun (_x : ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) => α -> β) (ContinuousOrderHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) g a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : TopologicalSpace.{u3} β] [_inst_4 : Preorder.{u3} β] [_inst_5 : TopologicalSpace.{u2} γ] [_inst_6 : Preorder.{u2} γ] (f : ContinuousOrderHom.{u3, u2} β γ _inst_4 _inst_6 _inst_3 _inst_5) (g : ContinuousOrderHom.{u1, u3} α β _inst_2 _inst_4 _inst_1 _inst_3) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => γ) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousOrderHom.{u1, u2} α γ _inst_2 _inst_6 _inst_1 _inst_5) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => γ) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousOrderHom.{u1, u2} α γ _inst_2 _inst_6 _inst_1 _inst_5) α γ _inst_1 _inst_5 (ContinuousOrderHomClass.toContinuousMapClass.{max u1 u2, u1, u2} (ContinuousOrderHom.{u1, u2} α γ _inst_2 _inst_6 _inst_1 _inst_5) α γ _inst_2 _inst_6 _inst_1 _inst_5 (ContinuousOrderHom.instContinuousOrderHomClassContinuousOrderHom.{u1, u2} α γ _inst_1 _inst_2 _inst_5 _inst_6))) (ContinuousOrderHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 f g) a) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (ContinuousOrderHom.{u3, u2} β γ _inst_4 _inst_6 _inst_3 _inst_5) β (fun (_x : β) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : β) => γ) _x) (ContinuousMapClass.toFunLike.{max u3 u2, u3, u2} (ContinuousOrderHom.{u3, u2} β γ _inst_4 _inst_6 _inst_3 _inst_5) β γ _inst_3 _inst_5 (ContinuousOrderHomClass.toContinuousMapClass.{max u3 u2, u3, u2} (ContinuousOrderHom.{u3, u2} β γ _inst_4 _inst_6 _inst_3 _inst_5) β γ _inst_4 _inst_6 _inst_3 _inst_5 (ContinuousOrderHom.instContinuousOrderHomClassContinuousOrderHom.{u3, u2} β γ _inst_3 _inst_4 _inst_5 _inst_6))) f (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (ContinuousOrderHom.{u1, u3} α β _inst_2 _inst_4 _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u3, u1, u3} (ContinuousOrderHom.{u1, u3} α β _inst_2 _inst_4 _inst_1 _inst_3) α β _inst_1 _inst_3 (ContinuousOrderHomClass.toContinuousMapClass.{max u1 u3, u1, u3} (ContinuousOrderHom.{u1, u3} α β _inst_2 _inst_4 _inst_1 _inst_3) α β _inst_2 _inst_4 _inst_1 _inst_3 (ContinuousOrderHom.instContinuousOrderHomClassContinuousOrderHom.{u1, u3} α β _inst_1 _inst_2 _inst_3 _inst_4))) g a))
Case conversion may be inaccurate. Consider using '#align continuous_order_hom.comp_apply ContinuousOrderHom.comp_applyₓ'. -/
@[simp]
theorem comp_apply (f : β →Co γ) (g : α →Co β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align continuous_order_hom.comp_apply ContinuousOrderHom.comp_apply

/- warning: continuous_order_hom.comp_assoc -> ContinuousOrderHom.comp_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : TopologicalSpace.{u2} β] [_inst_4 : Preorder.{u2} β] [_inst_5 : TopologicalSpace.{u3} γ] [_inst_6 : Preorder.{u3} γ] [_inst_7 : TopologicalSpace.{u4} δ] [_inst_8 : Preorder.{u4} δ] (f : ContinuousOrderHom.{u3, u4} γ δ _inst_6 _inst_8 _inst_5 _inst_7) (g : ContinuousOrderHom.{u2, u3} β γ _inst_4 _inst_6 _inst_3 _inst_5) (h : ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3), Eq.{max (succ u1) (succ u4)} (ContinuousOrderHom.{u1, u4} α δ _inst_2 _inst_8 _inst_1 _inst_7) (ContinuousOrderHom.comp.{u1, u2, u4} α β δ _inst_1 _inst_2 _inst_3 _inst_4 _inst_7 _inst_8 (ContinuousOrderHom.comp.{u2, u3, u4} β γ δ _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 _inst_8 f g) h) (ContinuousOrderHom.comp.{u1, u3, u4} α γ δ _inst_1 _inst_2 _inst_5 _inst_6 _inst_7 _inst_8 f (ContinuousOrderHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 g h))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u4}} {δ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : TopologicalSpace.{u2} β] [_inst_4 : Preorder.{u2} β] [_inst_5 : TopologicalSpace.{u4} γ] [_inst_6 : Preorder.{u4} γ] [_inst_7 : TopologicalSpace.{u3} δ] [_inst_8 : Preorder.{u3} δ] (f : ContinuousOrderHom.{u4, u3} γ δ _inst_6 _inst_8 _inst_5 _inst_7) (g : ContinuousOrderHom.{u2, u4} β γ _inst_4 _inst_6 _inst_3 _inst_5) (h : ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3), Eq.{max (succ u1) (succ u3)} (ContinuousOrderHom.{u1, u3} α δ _inst_2 _inst_8 _inst_1 _inst_7) (ContinuousOrderHom.comp.{u1, u2, u3} α β δ _inst_1 _inst_2 _inst_3 _inst_4 _inst_7 _inst_8 (ContinuousOrderHom.comp.{u2, u4, u3} β γ δ _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 _inst_8 f g) h) (ContinuousOrderHom.comp.{u1, u4, u3} α γ δ _inst_1 _inst_2 _inst_5 _inst_6 _inst_7 _inst_8 f (ContinuousOrderHom.comp.{u1, u2, u4} α β γ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 g h))
Case conversion may be inaccurate. Consider using '#align continuous_order_hom.comp_assoc ContinuousOrderHom.comp_assocₓ'. -/
@[simp]
theorem comp_assoc (f : γ →Co δ) (g : β →Co γ) (h : α →Co β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align continuous_order_hom.comp_assoc ContinuousOrderHom.comp_assoc

/- warning: continuous_order_hom.comp_id -> ContinuousOrderHom.comp_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : TopologicalSpace.{u2} β] [_inst_4 : Preorder.{u2} β] (f : ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3), Eq.{max (succ u1) (succ u2)} (ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) (ContinuousOrderHom.comp.{u1, u1, u2} α α β _inst_1 _inst_2 _inst_1 _inst_2 _inst_3 _inst_4 f (ContinuousOrderHom.id.{u1} α _inst_1 _inst_2)) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : TopologicalSpace.{u1} β] [_inst_4 : Preorder.{u1} β] (f : ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3), Eq.{max (succ u2) (succ u1)} (ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3) (ContinuousOrderHom.comp.{u2, u2, u1} α α β _inst_1 _inst_2 _inst_1 _inst_2 _inst_3 _inst_4 f (ContinuousOrderHom.id.{u2} α _inst_1 _inst_2)) f
Case conversion may be inaccurate. Consider using '#align continuous_order_hom.comp_id ContinuousOrderHom.comp_idₓ'. -/
@[simp]
theorem comp_id (f : α →Co β) : f.comp (ContinuousOrderHom.id α) = f :=
  ext fun a => rfl
#align continuous_order_hom.comp_id ContinuousOrderHom.comp_id

/- warning: continuous_order_hom.id_comp -> ContinuousOrderHom.id_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : TopologicalSpace.{u2} β] [_inst_4 : Preorder.{u2} β] (f : ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3), Eq.{max (succ u1) (succ u2)} (ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) (ContinuousOrderHom.comp.{u1, u2, u2} α β β _inst_1 _inst_2 _inst_3 _inst_4 _inst_3 _inst_4 (ContinuousOrderHom.id.{u2} β _inst_3 _inst_4) f) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : TopologicalSpace.{u1} β] [_inst_4 : Preorder.{u1} β] (f : ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3), Eq.{max (succ u2) (succ u1)} (ContinuousOrderHom.{u2, u1} α β _inst_2 _inst_4 _inst_1 _inst_3) (ContinuousOrderHom.comp.{u2, u1, u1} α β β _inst_1 _inst_2 _inst_3 _inst_4 _inst_3 _inst_4 (ContinuousOrderHom.id.{u1} β _inst_3 _inst_4) f) f
Case conversion may be inaccurate. Consider using '#align continuous_order_hom.id_comp ContinuousOrderHom.id_compₓ'. -/
@[simp]
theorem id_comp (f : α →Co β) : (ContinuousOrderHom.id β).comp f = f :=
  ext fun a => rfl
#align continuous_order_hom.id_comp ContinuousOrderHom.id_comp

/- warning: continuous_order_hom.cancel_right -> ContinuousOrderHom.cancel_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : TopologicalSpace.{u2} β] [_inst_4 : Preorder.{u2} β] [_inst_5 : TopologicalSpace.{u3} γ] [_inst_6 : Preorder.{u3} γ] {g₁ : ContinuousOrderHom.{u2, u3} β γ _inst_4 _inst_6 _inst_3 _inst_5} {g₂ : ContinuousOrderHom.{u2, u3} β γ _inst_4 _inst_6 _inst_3 _inst_5} {f : ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3}, (Function.Surjective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) (fun (_x : ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) => α -> β) (ContinuousOrderHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) f)) -> (Iff (Eq.{max (succ u1) (succ u3)} (ContinuousOrderHom.{u1, u3} α γ _inst_2 _inst_6 _inst_1 _inst_5) (ContinuousOrderHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 g₁ f) (ContinuousOrderHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 g₂ f)) (Eq.{max (succ u2) (succ u3)} (ContinuousOrderHom.{u2, u3} β γ _inst_4 _inst_6 _inst_3 _inst_5) g₁ g₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : TopologicalSpace.{u3} β] [_inst_4 : Preorder.{u3} β] [_inst_5 : TopologicalSpace.{u2} γ] [_inst_6 : Preorder.{u2} γ] {g₁ : ContinuousOrderHom.{u3, u2} β γ _inst_4 _inst_6 _inst_3 _inst_5} {g₂ : ContinuousOrderHom.{u3, u2} β γ _inst_4 _inst_6 _inst_3 _inst_5} {f : ContinuousOrderHom.{u1, u3} α β _inst_2 _inst_4 _inst_1 _inst_3}, (Function.Surjective.{succ u1, succ u3} α β (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (ContinuousOrderHom.{u1, u3} α β _inst_2 _inst_4 _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u3, u1, u3} (ContinuousOrderHom.{u1, u3} α β _inst_2 _inst_4 _inst_1 _inst_3) α β _inst_1 _inst_3 (ContinuousOrderHomClass.toContinuousMapClass.{max u1 u3, u1, u3} (ContinuousOrderHom.{u1, u3} α β _inst_2 _inst_4 _inst_1 _inst_3) α β _inst_2 _inst_4 _inst_1 _inst_3 (ContinuousOrderHom.instContinuousOrderHomClassContinuousOrderHom.{u1, u3} α β _inst_1 _inst_2 _inst_3 _inst_4))) f)) -> (Iff (Eq.{max (succ u1) (succ u2)} (ContinuousOrderHom.{u1, u2} α γ _inst_2 _inst_6 _inst_1 _inst_5) (ContinuousOrderHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 g₁ f) (ContinuousOrderHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 g₂ f)) (Eq.{max (succ u3) (succ u2)} (ContinuousOrderHom.{u3, u2} β γ _inst_4 _inst_6 _inst_3 _inst_5) g₁ g₂))
Case conversion may be inaccurate. Consider using '#align continuous_order_hom.cancel_right ContinuousOrderHom.cancel_rightₓ'. -/
theorem cancel_right {g₁ g₂ : β →Co γ} {f : α →Co β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align continuous_order_hom.cancel_right ContinuousOrderHom.cancel_right

/- warning: continuous_order_hom.cancel_left -> ContinuousOrderHom.cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : TopologicalSpace.{u2} β] [_inst_4 : Preorder.{u2} β] [_inst_5 : TopologicalSpace.{u3} γ] [_inst_6 : Preorder.{u3} γ] {g : ContinuousOrderHom.{u2, u3} β γ _inst_4 _inst_6 _inst_3 _inst_5} {f₁ : ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3} {f₂ : ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3}, (Function.Injective.{succ u2, succ u3} β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (ContinuousOrderHom.{u2, u3} β γ _inst_4 _inst_6 _inst_3 _inst_5) (fun (_x : ContinuousOrderHom.{u2, u3} β γ _inst_4 _inst_6 _inst_3 _inst_5) => β -> γ) (ContinuousOrderHom.hasCoeToFun.{u2, u3} β γ _inst_3 _inst_4 _inst_5 _inst_6) g)) -> (Iff (Eq.{max (succ u1) (succ u3)} (ContinuousOrderHom.{u1, u3} α γ _inst_2 _inst_6 _inst_1 _inst_5) (ContinuousOrderHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 g f₁) (ContinuousOrderHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 g f₂)) (Eq.{max (succ u1) (succ u2)} (ContinuousOrderHom.{u1, u2} α β _inst_2 _inst_4 _inst_1 _inst_3) f₁ f₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : TopologicalSpace.{u3} β] [_inst_4 : Preorder.{u3} β] [_inst_5 : TopologicalSpace.{u2} γ] [_inst_6 : Preorder.{u2} γ] {g : ContinuousOrderHom.{u3, u2} β γ _inst_4 _inst_6 _inst_3 _inst_5} {f₁ : ContinuousOrderHom.{u1, u3} α β _inst_2 _inst_4 _inst_1 _inst_3} {f₂ : ContinuousOrderHom.{u1, u3} α β _inst_2 _inst_4 _inst_1 _inst_3}, (Function.Injective.{succ u3, succ u2} β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (ContinuousOrderHom.{u3, u2} β γ _inst_4 _inst_6 _inst_3 _inst_5) β (fun (_x : β) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : β) => γ) _x) (ContinuousMapClass.toFunLike.{max u3 u2, u3, u2} (ContinuousOrderHom.{u3, u2} β γ _inst_4 _inst_6 _inst_3 _inst_5) β γ _inst_3 _inst_5 (ContinuousOrderHomClass.toContinuousMapClass.{max u3 u2, u3, u2} (ContinuousOrderHom.{u3, u2} β γ _inst_4 _inst_6 _inst_3 _inst_5) β γ _inst_4 _inst_6 _inst_3 _inst_5 (ContinuousOrderHom.instContinuousOrderHomClassContinuousOrderHom.{u3, u2} β γ _inst_3 _inst_4 _inst_5 _inst_6))) g)) -> (Iff (Eq.{max (succ u1) (succ u2)} (ContinuousOrderHom.{u1, u2} α γ _inst_2 _inst_6 _inst_1 _inst_5) (ContinuousOrderHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 g f₁) (ContinuousOrderHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 g f₂)) (Eq.{max (succ u1) (succ u3)} (ContinuousOrderHom.{u1, u3} α β _inst_2 _inst_4 _inst_1 _inst_3) f₁ f₂))
Case conversion may be inaccurate. Consider using '#align continuous_order_hom.cancel_left ContinuousOrderHom.cancel_leftₓ'. -/
theorem cancel_left {g : β →Co γ} {f₁ f₂ : α →Co β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align continuous_order_hom.cancel_left ContinuousOrderHom.cancel_left

instance : Preorder (α →Co β) :=
  Preorder.lift (coeFn : (α →Co β) → α → β)

end Preorder

instance [PartialOrder β] : PartialOrder (α →Co β) :=
  PartialOrder.lift _ FunLike.coe_injective

end ContinuousOrderHom

