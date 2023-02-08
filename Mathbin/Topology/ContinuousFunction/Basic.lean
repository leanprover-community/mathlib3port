/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri

! This file was ported from Lean 3 source module topology.continuous_function.basic
! leanprover-community/mathlib commit 98e83c3d541c77cdb7da20d79611a780ff8e7d90
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.UnionLift
import Mathbin.Topology.Homeomorph

/-!
# Continuous bundled maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define the type `continuous_map` of continuous bundled maps.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.
-/


open Function

#print ContinuousMap /-
/-- The type of continuous maps from `α` to `β`.

When possible, instead of parametrizing results over `(f : C(α, β))`,
you should parametrize over `{F : Type*} [continuous_map_class F α β] (f : F)`.

When you extend this structure, make sure to extend `continuous_map_class`. -/
@[protect_proj]
structure ContinuousMap (α β : Type _) [TopologicalSpace α] [TopologicalSpace β] where
  toFun : α → β
  continuous_toFun : Continuous to_fun := by continuity
#align continuous_map ContinuousMap
-/

-- mathport name: «exprC( , )»
notation "C(" α ", " β ")" => ContinuousMap α β

section

#print ContinuousMapClass /-
/-- `continuous_map_class F α β` states that `F` is a type of continuous maps.

You should extend this class when you extend `continuous_map`. -/
class ContinuousMapClass (F : Type _) (α β : outParam <| Type _) [TopologicalSpace α]
  [TopologicalSpace β] extends FunLike F α fun _ => β where
  map_continuous (f : F) : Continuous f
#align continuous_map_class ContinuousMapClass
-/

end

export ContinuousMapClass (map_continuous)

attribute [continuity] map_continuous

section ContinuousMapClass

variable {F α β : Type _} [TopologicalSpace α] [TopologicalSpace β] [ContinuousMapClass F α β]

include β

/- warning: map_continuous_at -> map_continuousAt is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : ContinuousMapClass.{u1, u2, u3} F α β _inst_1 _inst_2] (f : F) (a : α), ContinuousAt.{u2, u3} α β _inst_1 _inst_2 (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (ContinuousMapClass.toFunLike.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3)) f) a
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : ContinuousMapClass.{u1, u3, u2} F α β _inst_1 _inst_2] (f : F) (a : α), ContinuousAt.{u3, u2} α β _inst_1 _inst_2 (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{u1, u3, u2} F α β _inst_1 _inst_2 _inst_3) f) a
Case conversion may be inaccurate. Consider using '#align map_continuous_at map_continuousAtₓ'. -/
theorem map_continuousAt (f : F) (a : α) : ContinuousAt f a :=
  (map_continuous f).ContinuousAt
#align map_continuous_at map_continuousAt

/- warning: map_continuous_within_at -> map_continuousWithinAt is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : ContinuousMapClass.{u1, u2, u3} F α β _inst_1 _inst_2] (f : F) (s : Set.{u2} α) (a : α), ContinuousWithinAt.{u2, u3} α β _inst_1 _inst_2 (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (ContinuousMapClass.toFunLike.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3)) f) s a
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : ContinuousMapClass.{u1, u3, u2} F α β _inst_1 _inst_2] (f : F) (s : Set.{u3} α) (a : α), ContinuousWithinAt.{u3, u2} α β _inst_1 _inst_2 (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{u1, u3, u2} F α β _inst_1 _inst_2 _inst_3) f) s a
Case conversion may be inaccurate. Consider using '#align map_continuous_within_at map_continuousWithinAtₓ'. -/
theorem map_continuousWithinAt (f : F) (s : Set α) (a : α) : ContinuousWithinAt f s a :=
  (map_continuous f).ContinuousWithinAt
#align map_continuous_within_at map_continuousWithinAt

instance : CoeTC F C(α, β) :=
  ⟨fun f =>
    { toFun := f
      continuous_toFun := map_continuous f }⟩

end ContinuousMapClass

/-! ### Continuous maps-/


namespace ContinuousMap

variable {α β γ δ : Type _} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  [TopologicalSpace δ]

instance : ContinuousMapClass C(α, β) α β
    where
  coe := ContinuousMap.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_continuous := ContinuousMap.continuous_toFun

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun C(α, β) fun _ => α → β :=
  FunLike.hasCoeToFun

/- warning: continuous_map.to_fun_eq_coe -> ContinuousMap.toFun_eq_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2}, Eq.{max (succ u1) (succ u2)} (α -> β) (ContinuousMap.toFun.{u1, u2} α β _inst_1 _inst_2 f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : ContinuousMap.{u2, u1} α β _inst_1 _inst_2}, Eq.{max (succ u2) (succ u1)} (α -> β) (ContinuousMap.toFun.{u2, u1} α β _inst_1 _inst_2 f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) f)
Case conversion may be inaccurate. Consider using '#align continuous_map.to_fun_eq_coe ContinuousMap.toFun_eq_coeₓ'. -/
@[simp]
theorem toFun_eq_coe {f : C(α, β)} : f.toFun = (f : α → β) :=
  rfl
#align continuous_map.to_fun_eq_coe ContinuousMap.toFun_eq_coe

-- this must come after the coe_to_fun definition
initialize_simps_projections ContinuousMap (toFun → apply)

/- warning: continuous_map.coe_coe -> ContinuousMap.coe_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {F : Type.{u3}} [_inst_5 : ContinuousMapClass.{u3, u1, u2} F α β _inst_1 _inst_2] (f : F), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) ((fun (a : Type.{u3}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ u3, max (succ u1) (succ u2)} a b] => self.0) F (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (HasLiftT.mk.{succ u3, max (succ u1) (succ u2)} F (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (CoeTCₓ.coe.{succ u3, max (succ u1) (succ u2)} F (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.hasCoeT.{u3, u1, u2} F α β _inst_1 _inst_2 _inst_5))) f)) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F α (fun (_x : α) => β) (ContinuousMapClass.toFunLike.{u3, u1, u2} F α β _inst_1 _inst_2 _inst_5)) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {F : Type.{u3}} [_inst_5 : ContinuousMapClass.{u3, u2, u1} F α β _inst_1 _inst_2] (f : F), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (ContinuousMap.mk.{u2, u1} α β _inst_1 _inst_2 (FunLike.coe.{succ u3, succ u2, succ u1} F α (fun (a : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) a) (ContinuousMapClass.toFunLike.{u3, u2, u1} F α β _inst_1 _inst_2 _inst_5) f) (ContinuousMapClass.map_continuous.{u3, u2, u1} F α β _inst_1 _inst_2 _inst_5 f))) (FunLike.coe.{succ u3, succ u2, succ u1} F α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{u3, u2, u1} F α β _inst_1 _inst_2 _inst_5) f)
Case conversion may be inaccurate. Consider using '#align continuous_map.coe_coe ContinuousMap.coe_coeₓ'. -/
@[protected, simp, norm_cast]
theorem coe_coe {F : Type _} [ContinuousMapClass F α β] (f : F) : ⇑(f : C(α, β)) = f :=
  rfl
#align continuous_map.coe_coe ContinuousMap.coe_coe

/- warning: continuous_map.ext -> ContinuousMap.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2} {g : ContinuousMap.{u1, u2} α β _inst_1 _inst_2}, (forall (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g a)) -> (Eq.{max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : ContinuousMap.{u2, u1} α β _inst_1 _inst_2} {g : ContinuousMap.{u2, u1} α β _inst_1 _inst_2}, (forall (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) g a)) -> (Eq.{max (succ u2) (succ u1)} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align continuous_map.ext ContinuousMap.extₓ'. -/
@[ext]
theorem ext {f g : C(α, β)} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext _ _ h
#align continuous_map.ext ContinuousMap.ext

/- warning: continuous_map.copy -> ContinuousMap.copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)) -> (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) f)) -> (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align continuous_map.copy ContinuousMap.copyₓ'. -/
/-- Copy of a `continuous_map` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : C(α, β)) (f' : α → β) (h : f' = f) : C(α, β)
    where
  toFun := f'
  continuous_toFun := h.symm ▸ f.continuous_toFun
#align continuous_map.copy ContinuousMap.copy

/- warning: continuous_map.coe_copy -> ContinuousMap.coe_copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.copy.{u1, u2} α β _inst_1 _inst_2 f f' h)) f'
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : ContinuousMap.{u2, u1} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) f)), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (ContinuousMap.copy.{u2, u1} α β _inst_1 _inst_2 f f' h)) f'
Case conversion may be inaccurate. Consider using '#align continuous_map.coe_copy ContinuousMap.coe_copyₓ'. -/
@[simp]
theorem coe_copy (f : C(α, β)) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align continuous_map.coe_copy ContinuousMap.coe_copy

/- warning: continuous_map.copy_eq -> ContinuousMap.copy_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)), Eq.{max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.copy.{u1, u2} α β _inst_1 _inst_2 f f' h) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : ContinuousMap.{u2, u1} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) f)), Eq.{max (succ u2) (succ u1)} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) (ContinuousMap.copy.{u2, u1} α β _inst_1 _inst_2 f f' h) f
Case conversion may be inaccurate. Consider using '#align continuous_map.copy_eq ContinuousMap.copy_eqₓ'. -/
theorem copy_eq (f : C(α, β)) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align continuous_map.copy_eq ContinuousMap.copy_eq

variable {α β} {f g : C(α, β)}

/- warning: continuous_map.continuous -> ContinuousMap.continuous is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Continuous.{u1, u2} α β _inst_1 _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : ContinuousMap.{u2, u1} α β _inst_1 _inst_2), Continuous.{u2, u1} α β _inst_1 _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) f)
Case conversion may be inaccurate. Consider using '#align continuous_map.continuous ContinuousMap.continuousₓ'. -/
/-- Deprecated. Use `map_continuous` instead. -/
protected theorem continuous (f : C(α, β)) : Continuous f :=
  f.continuous_toFun
#align continuous_map.continuous ContinuousMap.continuous

/- warning: continuous_map.continuous_set_coe -> ContinuousMap.continuous_set_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (s : Set.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (f : coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) s), Continuous.{u1, u2} α β _inst_1 _inst_2 (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) s) (fun (x : coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) s) => α -> β) (coeFnTrans.{max (succ u1) (succ u2), succ (max u1 u2), succ (max u1 u2)} (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) s) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (coeBaseAux.{succ (max u1 u2), succ (max u1 u2)} (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) s) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (coeSubtype.{succ (max u1 u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => Membership.Mem.{max u1 u2, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (Set.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (Set.hasMem.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) x s)))) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (s : Set.{max u2 u1} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (f : Set.Elem.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) s), Continuous.{u1, u2} α β _inst_1 _inst_2 (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (Subtype.val.{max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => Membership.mem.{max u1 u2, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (Set.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (Set.instMembershipSet.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) x s) f))
Case conversion may be inaccurate. Consider using '#align continuous_map.continuous_set_coe ContinuousMap.continuous_set_coeₓ'. -/
@[continuity]
theorem continuous_set_coe (s : Set C(α, β)) (f : s) : Continuous f :=
  f.1.Continuous
#align continuous_map.continuous_set_coe ContinuousMap.continuous_set_coe

/- warning: continuous_map.continuous_at -> ContinuousMap.continuousAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (x : α), ContinuousAt.{u1, u2} α β _inst_1 _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f) x
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : ContinuousMap.{u2, u1} α β _inst_1 _inst_2) (x : α), ContinuousAt.{u2, u1} α β _inst_1 _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) f) x
Case conversion may be inaccurate. Consider using '#align continuous_map.continuous_at ContinuousMap.continuousAtₓ'. -/
/-- Deprecated. Use `map_continuous_at` instead. -/
protected theorem continuousAt (f : C(α, β)) (x : α) : ContinuousAt f x :=
  f.Continuous.ContinuousAt
#align continuous_map.continuous_at ContinuousMap.continuousAt

/- warning: continuous_map.congr_fun -> ContinuousMap.congr_fun is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2} {g : ContinuousMap.{u1, u2} α β _inst_1 _inst_2}, (Eq.{max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) f g) -> (forall (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : ContinuousMap.{u2, u1} α β _inst_1 _inst_2} {g : ContinuousMap.{u2, u1} α β _inst_1 _inst_2}, (Eq.{max (succ u2) (succ u1)} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) f g) -> (forall (x : α), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) g x))
Case conversion may be inaccurate. Consider using '#align continuous_map.congr_fun ContinuousMap.congr_funₓ'. -/
/-- Deprecated. Use `fun_like.congr_fun` instead. -/
protected theorem congr_fun {f g : C(α, β)} (H : f = g) (x : α) : f x = g x :=
  H ▸ rfl
#align continuous_map.congr_fun ContinuousMap.congr_fun

/- warning: continuous_map.congr_arg -> ContinuousMap.congr_arg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) {x : α} {y : α}, (Eq.{succ u1} α x y) -> (Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f y))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : ContinuousMap.{u2, u1} α β _inst_1 _inst_2) {x : α} {y : α}, (Eq.{succ u2} α x y) -> (Eq.{succ u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) f y))
Case conversion may be inaccurate. Consider using '#align continuous_map.congr_arg ContinuousMap.congr_argₓ'. -/
/-- Deprecated. Use `fun_like.congr_arg` instead. -/
protected theorem congr_arg (f : C(α, β)) {x y : α} (h : x = y) : f x = f y :=
  h ▸ rfl
#align continuous_map.congr_arg ContinuousMap.congr_arg

/- warning: continuous_map.coe_injective -> ContinuousMap.coe_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Function.Injective.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (ᾰ : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Function.Injective.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (α -> β) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (ᾰ : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) ᾰ) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)))
Case conversion may be inaccurate. Consider using '#align continuous_map.coe_injective ContinuousMap.coe_injectiveₓ'. -/
theorem coe_injective : @Function.Injective C(α, β) (α → β) coeFn := fun f g h => by
  cases f <;> cases g <;> congr
#align continuous_map.coe_injective ContinuousMap.coe_injective

/- warning: continuous_map.coe_mk -> ContinuousMap.coe_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : α -> β) (h : Continuous.{u1, u2} α β _inst_1 _inst_2 f), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.mk.{u1, u2} α β _inst_1 _inst_2 f h)) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : α -> β) (h : Continuous.{u2, u1} α β _inst_1 _inst_2 f), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (ContinuousMap.mk.{u2, u1} α β _inst_1 _inst_2 f h)) f
Case conversion may be inaccurate. Consider using '#align continuous_map.coe_mk ContinuousMap.coe_mkₓ'. -/
@[simp]
theorem coe_mk (f : α → β) (h : Continuous f) : ⇑(⟨f, h⟩ : C(α, β)) = f :=
  rfl
#align continuous_map.coe_mk ContinuousMap.coe_mk

/- warning: continuous_map.map_specializes -> ContinuousMap.map_specializes is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) {x : α} {y : α}, (Specializes.{u1} α _inst_1 x y) -> (Specializes.{u2} β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f y))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : ContinuousMap.{u2, u1} α β _inst_1 _inst_2) {x : α} {y : α}, (Specializes.{u2} α _inst_1 x y) -> (Specializes.{u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) x) _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) f y))
Case conversion may be inaccurate. Consider using '#align continuous_map.map_specializes ContinuousMap.map_specializesₓ'. -/
theorem map_specializes (f : C(α, β)) {x y : α} (h : x ⤳ y) : f x ⤳ f y :=
  h.map f.2
#align continuous_map.map_specializes ContinuousMap.map_specializes

section

variable (α β)

#print ContinuousMap.equivFnOfDiscrete /-
/--
The continuous functions from `α` to `β` are the same as the plain functions when `α` is discrete.
-/
@[simps]
def equivFnOfDiscrete [DiscreteTopology α] : C(α, β) ≃ (α → β) :=
  ⟨fun f => f, fun f => ⟨f, continuous_of_discreteTopology⟩, fun f =>
    by
    ext
    rfl, fun f => by
    ext
    rfl⟩
#align continuous_map.equiv_fn_of_discrete ContinuousMap.equivFnOfDiscrete
-/

end

variable (α)

#print ContinuousMap.id /-
/-- The identity as a continuous map. -/
protected def id : C(α, α) :=
  ⟨id⟩
#align continuous_map.id ContinuousMap.id
-/

/- warning: continuous_map.coe_id -> ContinuousMap.coe_id is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} α], Eq.{succ u1} (α -> α) (coeFn.{succ u1, succ u1} (ContinuousMap.{u1, u1} α α _inst_1 _inst_1) (fun (_x : ContinuousMap.{u1, u1} α α _inst_1 _inst_1) => α -> α) (ContinuousMap.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (ContinuousMap.id.{u1} α _inst_1)) (id.{succ u1} α)
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} α], Eq.{succ u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => α) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (ContinuousMap.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => α) _x) (ContinuousMapClass.toFunLike.{u1, u1, u1} (ContinuousMap.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u1} α α _inst_1 _inst_1)) (ContinuousMap.id.{u1} α _inst_1)) (id.{succ u1} α)
Case conversion may be inaccurate. Consider using '#align continuous_map.coe_id ContinuousMap.coe_idₓ'. -/
@[simp]
theorem coe_id : ⇑(ContinuousMap.id α) = id :=
  rfl
#align continuous_map.coe_id ContinuousMap.coe_id

#print ContinuousMap.const /-
/-- The constant map as a continuous map. -/
def const (b : β) : C(α, β) :=
  ⟨const α b⟩
#align continuous_map.const ContinuousMap.const
-/

/- warning: continuous_map.coe_const -> ContinuousMap.coe_const is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (b : β), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.const.{u1, u2} α β _inst_1 _inst_2 b)) (Function.const.{succ u2, succ u1} β α b)
but is expected to have type
  forall (α : Type.{u2}) {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (b : β), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (ContinuousMap.const.{u2, u1} α β _inst_1 _inst_2 b)) (Function.const.{succ u1, succ u2} β α b)
Case conversion may be inaccurate. Consider using '#align continuous_map.coe_const ContinuousMap.coe_constₓ'. -/
@[simp]
theorem coe_const (b : β) : ⇑(const α b) = Function.const α b :=
  rfl
#align continuous_map.coe_const ContinuousMap.coe_const

instance [Inhabited β] : Inhabited C(α, β) :=
  ⟨const α default⟩

variable {α}

/- warning: continuous_map.id_apply -> ContinuousMap.id_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (ContinuousMap.{u1, u1} α α _inst_1 _inst_1) (fun (_x : ContinuousMap.{u1, u1} α α _inst_1 _inst_1) => α -> α) (ContinuousMap.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (ContinuousMap.id.{u1} α _inst_1) a) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (ContinuousMap.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => α) _x) (ContinuousMapClass.toFunLike.{u1, u1, u1} (ContinuousMap.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u1} α α _inst_1 _inst_1)) (ContinuousMap.id.{u1} α _inst_1) a) a
Case conversion may be inaccurate. Consider using '#align continuous_map.id_apply ContinuousMap.id_applyₓ'. -/
@[simp]
theorem id_apply (a : α) : ContinuousMap.id α a = a :=
  rfl
#align continuous_map.id_apply ContinuousMap.id_apply

/- warning: continuous_map.const_apply -> ContinuousMap.const_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (b : β) (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.const.{u1, u2} α β _inst_1 _inst_2 b) a) b
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (b : β) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (ContinuousMap.const.{u1, u2} α β _inst_1 _inst_2 b) a) b
Case conversion may be inaccurate. Consider using '#align continuous_map.const_apply ContinuousMap.const_applyₓ'. -/
@[simp]
theorem const_apply (b : β) (a : α) : const α b a = b :=
  rfl
#align continuous_map.const_apply ContinuousMap.const_apply

#print ContinuousMap.comp /-
/-- The composition of continuous maps, as a continuous map. -/
def comp (f : C(β, γ)) (g : C(α, β)) : C(α, γ) :=
  ⟨f ∘ g⟩
#align continuous_map.comp ContinuousMap.comp
-/

/- warning: continuous_map.coe_comp -> ContinuousMap.coe_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (f : ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (g : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (α -> γ) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (ContinuousMap.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g)) (Function.comp.{succ u1, succ u2, succ u3} α β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (ContinuousMap.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] (f : ContinuousMap.{u3, u2} β γ _inst_2 _inst_3) (g : ContinuousMap.{u1, u3} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => γ) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => γ) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α γ _inst_1 _inst_3)) (ContinuousMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g)) (Function.comp.{succ u1, succ u3, succ u2} α β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (ContinuousMap.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : β) => γ) _x) (ContinuousMapClass.toFunLike.{max u3 u2, u3, u2} (ContinuousMap.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (ContinuousMap.instContinuousMapClassContinuousMap.{u3, u2} β γ _inst_2 _inst_3)) f) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (ContinuousMap.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u3, u1, u3} (ContinuousMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u3} α β _inst_1 _inst_2)) g))
Case conversion may be inaccurate. Consider using '#align continuous_map.coe_comp ContinuousMap.coe_compₓ'. -/
@[simp]
theorem coe_comp (f : C(β, γ)) (g : C(α, β)) : ⇑(comp f g) = f ∘ g :=
  rfl
#align continuous_map.coe_comp ContinuousMap.coe_comp

/- warning: continuous_map.comp_apply -> ContinuousMap.comp_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (f : ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (g : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (a : α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (ContinuousMap.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g) a) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (ContinuousMap.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] (f : ContinuousMap.{u3, u2} β γ _inst_2 _inst_3) (g : ContinuousMap.{u1, u3} α β _inst_1 _inst_2) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => γ) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => γ) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α γ _inst_1 _inst_3)) (ContinuousMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g) a) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (ContinuousMap.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : β) => γ) _x) (ContinuousMapClass.toFunLike.{max u3 u2, u3, u2} (ContinuousMap.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (ContinuousMap.instContinuousMapClassContinuousMap.{u3, u2} β γ _inst_2 _inst_3)) f (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (ContinuousMap.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u3, u1, u3} (ContinuousMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u3} α β _inst_1 _inst_2)) g a))
Case conversion may be inaccurate. Consider using '#align continuous_map.comp_apply ContinuousMap.comp_applyₓ'. -/
@[simp]
theorem comp_apply (f : C(β, γ)) (g : C(α, β)) (a : α) : comp f g a = f (g a) :=
  rfl
#align continuous_map.comp_apply ContinuousMap.comp_apply

/- warning: continuous_map.comp_assoc -> ContinuousMap.comp_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] (f : ContinuousMap.{u3, u4} γ δ _inst_3 _inst_4) (g : ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (h : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u4)} (ContinuousMap.{u1, u4} α δ _inst_1 _inst_4) (ContinuousMap.comp.{u1, u2, u4} α β δ _inst_1 _inst_2 _inst_4 (ContinuousMap.comp.{u2, u3, u4} β γ δ _inst_2 _inst_3 _inst_4 f g) h) (ContinuousMap.comp.{u1, u3, u4} α γ δ _inst_1 _inst_3 _inst_4 f (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g h))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u4}} {δ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u4} γ] [_inst_4 : TopologicalSpace.{u3} δ] (f : ContinuousMap.{u4, u3} γ δ _inst_3 _inst_4) (g : ContinuousMap.{u2, u4} β γ _inst_2 _inst_3) (h : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (ContinuousMap.{u1, u3} α δ _inst_1 _inst_4) (ContinuousMap.comp.{u1, u2, u3} α β δ _inst_1 _inst_2 _inst_4 (ContinuousMap.comp.{u2, u4, u3} β γ δ _inst_2 _inst_3 _inst_4 f g) h) (ContinuousMap.comp.{u1, u4, u3} α γ δ _inst_1 _inst_3 _inst_4 f (ContinuousMap.comp.{u1, u2, u4} α β γ _inst_1 _inst_2 _inst_3 g h))
Case conversion may be inaccurate. Consider using '#align continuous_map.comp_assoc ContinuousMap.comp_assocₓ'. -/
@[simp]
theorem comp_assoc (f : C(γ, δ)) (g : C(β, γ)) (h : C(α, β)) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align continuous_map.comp_assoc ContinuousMap.comp_assoc

/- warning: continuous_map.id_comp -> ContinuousMap.id_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.comp.{u1, u2, u2} α β β _inst_1 _inst_2 _inst_2 (ContinuousMap.id.{u2} β _inst_2) f) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : ContinuousMap.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) (ContinuousMap.comp.{u2, u1, u1} α β β _inst_1 _inst_2 _inst_2 (ContinuousMap.id.{u1} β _inst_2) f) f
Case conversion may be inaccurate. Consider using '#align continuous_map.id_comp ContinuousMap.id_compₓ'. -/
@[simp]
theorem id_comp (f : C(α, β)) : (ContinuousMap.id _).comp f = f :=
  ext fun _ => rfl
#align continuous_map.id_comp ContinuousMap.id_comp

/- warning: continuous_map.comp_id -> ContinuousMap.comp_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.comp.{u1, u1, u2} α α β _inst_1 _inst_1 _inst_2 f (ContinuousMap.id.{u1} α _inst_1)) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : ContinuousMap.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) (ContinuousMap.comp.{u2, u2, u1} α α β _inst_1 _inst_1 _inst_2 f (ContinuousMap.id.{u2} α _inst_1)) f
Case conversion may be inaccurate. Consider using '#align continuous_map.comp_id ContinuousMap.comp_idₓ'. -/
@[simp]
theorem comp_id (f : C(α, β)) : f.comp (ContinuousMap.id _) = f :=
  ext fun _ => rfl
#align continuous_map.comp_id ContinuousMap.comp_id

/- warning: continuous_map.const_comp -> ContinuousMap.const_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (c : γ) (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 (ContinuousMap.const.{u2, u3} β γ _inst_2 _inst_3 c) f) (ContinuousMap.const.{u1, u3} α γ _inst_1 _inst_3 c)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] (c : γ) (f : ContinuousMap.{u3, u2} α β _inst_1 _inst_2), Eq.{max (succ u3) (succ u1)} (ContinuousMap.{u3, u1} α γ _inst_1 _inst_3) (ContinuousMap.comp.{u3, u2, u1} α β γ _inst_1 _inst_2 _inst_3 (ContinuousMap.const.{u2, u1} β γ _inst_2 _inst_3 c) f) (ContinuousMap.const.{u3, u1} α γ _inst_1 _inst_3 c)
Case conversion may be inaccurate. Consider using '#align continuous_map.const_comp ContinuousMap.const_compₓ'. -/
@[simp]
theorem const_comp (c : γ) (f : C(α, β)) : (const β c).comp f = const α c :=
  ext fun _ => rfl
#align continuous_map.const_comp ContinuousMap.const_comp

/- warning: continuous_map.comp_const -> ContinuousMap.comp_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (f : ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (b : β), Eq.{max (succ u1) (succ u3)} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f (ContinuousMap.const.{u1, u2} α β _inst_1 _inst_2 b)) (ContinuousMap.const.{u1, u3} α γ _inst_1 _inst_3 (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (ContinuousMap.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] (f : ContinuousMap.{u3, u2} β γ _inst_2 _inst_3) (b : β), Eq.{max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α γ _inst_1 _inst_3) (ContinuousMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f (ContinuousMap.const.{u1, u3} α β _inst_1 _inst_2 b)) (ContinuousMap.const.{u1, u2} α ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : β) => γ) b) _inst_1 _inst_3 (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (ContinuousMap.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : β) => γ) _x) (ContinuousMapClass.toFunLike.{max u3 u2, u3, u2} (ContinuousMap.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (ContinuousMap.instContinuousMapClassContinuousMap.{u3, u2} β γ _inst_2 _inst_3)) f b))
Case conversion may be inaccurate. Consider using '#align continuous_map.comp_const ContinuousMap.comp_constₓ'. -/
@[simp]
theorem comp_const (f : C(β, γ)) (b : β) : f.comp (const α b) = const α (f b) :=
  ext fun _ => rfl
#align continuous_map.comp_const ContinuousMap.comp_const

/- warning: continuous_map.cancel_right -> ContinuousMap.cancel_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f₁ : ContinuousMap.{u2, u3} β γ _inst_2 _inst_3} {f₂ : ContinuousMap.{u2, u3} β γ _inst_2 _inst_3} {g : ContinuousMap.{u1, u2} α β _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g)) -> (Iff (Eq.{max (succ u1) (succ u3)} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f₁ g) (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f₂ g)) (Eq.{max (succ u2) (succ u3)} (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) f₁ f₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] {f₁ : ContinuousMap.{u3, u2} β γ _inst_2 _inst_3} {f₂ : ContinuousMap.{u3, u2} β γ _inst_2 _inst_3} {g : ContinuousMap.{u1, u3} α β _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u3} α β (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (ContinuousMap.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u3, u1, u3} (ContinuousMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u3} α β _inst_1 _inst_2)) g)) -> (Iff (Eq.{max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α γ _inst_1 _inst_3) (ContinuousMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f₁ g) (ContinuousMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f₂ g)) (Eq.{max (succ u3) (succ u2)} (ContinuousMap.{u3, u2} β γ _inst_2 _inst_3) f₁ f₂))
Case conversion may be inaccurate. Consider using '#align continuous_map.cancel_right ContinuousMap.cancel_rightₓ'. -/
theorem cancel_right {f₁ f₂ : C(β, γ)} {g : C(α, β)} (hg : Surjective g) :
    f₁.comp g = f₂.comp g ↔ f₁ = f₂ :=
  ⟨fun h => ext <| hg.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align continuous_map.cancel_right ContinuousMap.cancel_right

/- warning: continuous_map.cancel_left -> ContinuousMap.cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : ContinuousMap.{u2, u3} β γ _inst_2 _inst_3} {g₁ : ContinuousMap.{u1, u2} α β _inst_1 _inst_2} {g₂ : ContinuousMap.{u1, u2} α β _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u3} β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (ContinuousMap.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f)) -> (Iff (Eq.{max (succ u1) (succ u3)} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g₁) (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g₂)) (Eq.{max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) g₁ g₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] {f : ContinuousMap.{u3, u2} β γ _inst_2 _inst_3} {g₁ : ContinuousMap.{u1, u3} α β _inst_1 _inst_2} {g₂ : ContinuousMap.{u1, u3} α β _inst_1 _inst_2}, (Function.Injective.{succ u3, succ u2} β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (ContinuousMap.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : β) => γ) _x) (ContinuousMapClass.toFunLike.{max u3 u2, u3, u2} (ContinuousMap.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (ContinuousMap.instContinuousMapClassContinuousMap.{u3, u2} β γ _inst_2 _inst_3)) f)) -> (Iff (Eq.{max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α γ _inst_1 _inst_3) (ContinuousMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g₁) (ContinuousMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g₂)) (Eq.{max (succ u1) (succ u3)} (ContinuousMap.{u1, u3} α β _inst_1 _inst_2) g₁ g₂))
Case conversion may be inaccurate. Consider using '#align continuous_map.cancel_left ContinuousMap.cancel_leftₓ'. -/
theorem cancel_left {f : C(β, γ)} {g₁ g₂ : C(α, β)} (hf : Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
  ⟨fun h => ext fun a => hf <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align continuous_map.cancel_left ContinuousMap.cancel_left

instance [Nonempty α] [Nontrivial β] : Nontrivial C(α, β) :=
  ⟨let ⟨b₁, b₂, hb⟩ := exists_pair_ne β
    ⟨const _ b₁, const _ b₂, fun h => hb <| FunLike.congr_fun h <| Classical.arbitrary α⟩⟩

section Prod

variable {α₁ α₂ β₁ β₂ : Type _} [TopologicalSpace α₁] [TopologicalSpace α₂] [TopologicalSpace β₁]
  [TopologicalSpace β₂]

/- warning: continuous_map.prod_mk -> ContinuousMap.prodMk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β₁ : Type.{u2}} {β₂ : Type.{u3}} [_inst_7 : TopologicalSpace.{u2} β₁] [_inst_8 : TopologicalSpace.{u3} β₂], (ContinuousMap.{u1, u2} α β₁ _inst_1 _inst_7) -> (ContinuousMap.{u1, u3} α β₂ _inst_1 _inst_8) -> (ContinuousMap.{u1, max u2 u3} α (Prod.{u2, u3} β₁ β₂) _inst_1 (Prod.topologicalSpace.{u2, u3} β₁ β₂ _inst_7 _inst_8))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β₁ : Type.{u2}} {β₂ : Type.{u3}} [_inst_7 : TopologicalSpace.{u2} β₁] [_inst_8 : TopologicalSpace.{u3} β₂], (ContinuousMap.{u1, u2} α β₁ _inst_1 _inst_7) -> (ContinuousMap.{u1, u3} α β₂ _inst_1 _inst_8) -> (ContinuousMap.{u1, max u3 u2} α (Prod.{u2, u3} β₁ β₂) _inst_1 (instTopologicalSpaceProd.{u2, u3} β₁ β₂ _inst_7 _inst_8))
Case conversion may be inaccurate. Consider using '#align continuous_map.prod_mk ContinuousMap.prodMkₓ'. -/
/-- Given two continuous maps `f` and `g`, this is the continuous map `x ↦ (f x, g x)`. -/
def prodMk (f : C(α, β₁)) (g : C(α, β₂)) : C(α, β₁ × β₂)
    where
  toFun x := (f x, g x)
  continuous_toFun := Continuous.prod_mk f.Continuous g.Continuous
#align continuous_map.prod_mk ContinuousMap.prodMk

/- warning: continuous_map.prod_map -> ContinuousMap.prodMap is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {α₂ : Type.{u2}} {β₁ : Type.{u3}} {β₂ : Type.{u4}} [_inst_5 : TopologicalSpace.{u1} α₁] [_inst_6 : TopologicalSpace.{u2} α₂] [_inst_7 : TopologicalSpace.{u3} β₁] [_inst_8 : TopologicalSpace.{u4} β₂], (ContinuousMap.{u1, u2} α₁ α₂ _inst_5 _inst_6) -> (ContinuousMap.{u3, u4} β₁ β₂ _inst_7 _inst_8) -> (ContinuousMap.{max u1 u3, max u2 u4} (Prod.{u1, u3} α₁ β₁) (Prod.{u2, u4} α₂ β₂) (Prod.topologicalSpace.{u1, u3} α₁ β₁ _inst_5 _inst_7) (Prod.topologicalSpace.{u2, u4} α₂ β₂ _inst_6 _inst_8))
but is expected to have type
  forall {α₁ : Type.{u1}} {α₂ : Type.{u2}} {β₁ : Type.{u3}} {β₂ : Type.{u4}} [_inst_5 : TopologicalSpace.{u1} α₁] [_inst_6 : TopologicalSpace.{u2} α₂] [_inst_7 : TopologicalSpace.{u3} β₁] [_inst_8 : TopologicalSpace.{u4} β₂], (ContinuousMap.{u1, u2} α₁ α₂ _inst_5 _inst_6) -> (ContinuousMap.{u3, u4} β₁ β₂ _inst_7 _inst_8) -> (ContinuousMap.{max u3 u1, max u4 u2} (Prod.{u1, u3} α₁ β₁) (Prod.{u2, u4} α₂ β₂) (instTopologicalSpaceProd.{u1, u3} α₁ β₁ _inst_5 _inst_7) (instTopologicalSpaceProd.{u2, u4} α₂ β₂ _inst_6 _inst_8))
Case conversion may be inaccurate. Consider using '#align continuous_map.prod_map ContinuousMap.prodMapₓ'. -/
/-- Given two continuous maps `f` and `g`, this is the continuous map `(x, y) ↦ (f x, g y)`. -/
@[simps]
def prodMap (f : C(α₁, α₂)) (g : C(β₁, β₂)) : C(α₁ × β₁, α₂ × β₂)
    where
  toFun := Prod.map f g
  continuous_toFun := Continuous.prod_map f.Continuous g.Continuous
#align continuous_map.prod_map ContinuousMap.prodMap

/- warning: continuous_map.prod_eval -> ContinuousMap.prod_eval is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β₁ : Type.{u2}} {β₂ : Type.{u3}} [_inst_7 : TopologicalSpace.{u2} β₁] [_inst_8 : TopologicalSpace.{u3} β₂] (f : ContinuousMap.{u1, u2} α β₁ _inst_1 _inst_7) (g : ContinuousMap.{u1, u3} α β₂ _inst_1 _inst_8) (a : α), Eq.{max (succ u2) (succ u3)} (Prod.{u2, u3} β₁ β₂) (coeFn.{max (succ u1) (succ (max u2 u3)), max (succ u1) (succ (max u2 u3))} (ContinuousMap.{u1, max u2 u3} α (Prod.{u2, u3} β₁ β₂) _inst_1 (Prod.topologicalSpace.{u2, u3} β₁ β₂ _inst_7 _inst_8)) (fun (_x : ContinuousMap.{u1, max u2 u3} α (Prod.{u2, u3} β₁ β₂) _inst_1 (Prod.topologicalSpace.{u2, u3} β₁ β₂ _inst_7 _inst_8)) => α -> (Prod.{u2, u3} β₁ β₂)) (ContinuousMap.hasCoeToFun.{u1, max u2 u3} α (Prod.{u2, u3} β₁ β₂) _inst_1 (Prod.topologicalSpace.{u2, u3} β₁ β₂ _inst_7 _inst_8)) (ContinuousMap.prodMk.{u1, u2, u3} α _inst_1 β₁ β₂ _inst_7 _inst_8 f g) a) (Prod.mk.{u2, u3} β₁ β₂ (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β₁ _inst_1 _inst_7) (fun (_x : ContinuousMap.{u1, u2} α β₁ _inst_1 _inst_7) => α -> β₁) (ContinuousMap.hasCoeToFun.{u1, u2} α β₁ _inst_1 _inst_7) f a) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (ContinuousMap.{u1, u3} α β₂ _inst_1 _inst_8) (fun (_x : ContinuousMap.{u1, u3} α β₂ _inst_1 _inst_8) => α -> β₂) (ContinuousMap.hasCoeToFun.{u1, u3} α β₂ _inst_1 _inst_8) g a))
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] {β₁ : Type.{u2}} {β₂ : Type.{u1}} [_inst_7 : TopologicalSpace.{u2} β₁] [_inst_8 : TopologicalSpace.{u1} β₂] (f : ContinuousMap.{u3, u2} α β₁ _inst_1 _inst_7) (g : ContinuousMap.{u3, u1} α β₂ _inst_1 _inst_8) (a : α), Eq.{max (succ u2) (succ u1)} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => Prod.{u2, u1} β₁ β₂) a) (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), succ u3, max (succ u2) (succ u1)} (ContinuousMap.{u3, max u1 u2} α (Prod.{u2, u1} β₁ β₂) _inst_1 (instTopologicalSpaceProd.{u2, u1} β₁ β₂ _inst_7 _inst_8)) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => Prod.{u2, u1} β₁ β₂) _x) (ContinuousMapClass.toFunLike.{max (max u3 u2) u1, u3, max u2 u1} (ContinuousMap.{u3, max u1 u2} α (Prod.{u2, u1} β₁ β₂) _inst_1 (instTopologicalSpaceProd.{u2, u1} β₁ β₂ _inst_7 _inst_8)) α (Prod.{u2, u1} β₁ β₂) _inst_1 (instTopologicalSpaceProd.{u2, u1} β₁ β₂ _inst_7 _inst_8) (ContinuousMap.instContinuousMapClassContinuousMap.{u3, max u2 u1} α (Prod.{u2, u1} β₁ β₂) _inst_1 (instTopologicalSpaceProd.{u2, u1} β₁ β₂ _inst_7 _inst_8))) (ContinuousMap.prodMk.{u3, u2, u1} α _inst_1 β₁ β₂ _inst_7 _inst_8 f g) a) (Prod.mk.{u2, u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β₁) a) ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β₂) a) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (ContinuousMap.{u3, u2} α β₁ _inst_1 _inst_7) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β₁) _x) (ContinuousMapClass.toFunLike.{max u3 u2, u3, u2} (ContinuousMap.{u3, u2} α β₁ _inst_1 _inst_7) α β₁ _inst_1 _inst_7 (ContinuousMap.instContinuousMapClassContinuousMap.{u3, u2} α β₁ _inst_1 _inst_7)) f a) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (ContinuousMap.{u3, u1} α β₂ _inst_1 _inst_8) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β₂) _x) (ContinuousMapClass.toFunLike.{max u3 u1, u3, u1} (ContinuousMap.{u3, u1} α β₂ _inst_1 _inst_8) α β₂ _inst_1 _inst_8 (ContinuousMap.instContinuousMapClassContinuousMap.{u3, u1} α β₂ _inst_1 _inst_8)) g a))
Case conversion may be inaccurate. Consider using '#align continuous_map.prod_eval ContinuousMap.prod_evalₓ'. -/
@[simp]
theorem prod_eval (f : C(α, β₁)) (g : C(α, β₂)) (a : α) : (prodMk f g) a = (f a, g a) :=
  rfl
#align continuous_map.prod_eval ContinuousMap.prod_eval

end Prod

section Pi

variable {I A : Type _} {X : I → Type _} [TopologicalSpace A] [∀ i, TopologicalSpace (X i)]

#print ContinuousMap.pi /-
/-- Abbreviation for product of continuous maps, which is continuous -/
def pi (f : ∀ i, C(A, X i)) : C(A, ∀ i, X i) where toFun (a : A) (i : I) := f i a
#align continuous_map.pi ContinuousMap.pi
-/

/- warning: continuous_map.pi_eval -> ContinuousMap.pi_eval is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {A : Type.{u2}} {X : I -> Type.{u3}} [_inst_5 : TopologicalSpace.{u2} A] [_inst_6 : forall (i : I), TopologicalSpace.{u3} (X i)] (f : forall (i : I), ContinuousMap.{u2, u3} A (X i) _inst_5 (_inst_6 i)) (a : A), Eq.{max (succ u1) (succ u3)} (forall (i : I), (fun (i : I) => X i) i) (coeFn.{max (succ u2) (succ (max u1 u3)), max (succ u2) (succ (max u1 u3))} (ContinuousMap.{u2, max u1 u3} A (forall (i : I), (fun (i : I) => X i) i) _inst_5 (Pi.topologicalSpace.{u1, u3} I (fun (i : I) => (fun (i : I) => X i) i) (fun (a : I) => (fun (i : I) => _inst_6 i) a))) (fun (_x : ContinuousMap.{u2, max u1 u3} A (forall (i : I), (fun (i : I) => X i) i) _inst_5 (Pi.topologicalSpace.{u1, u3} I (fun (i : I) => (fun (i : I) => X i) i) (fun (a : I) => (fun (i : I) => _inst_6 i) a))) => A -> (forall (i : I), (fun (i : I) => X i) i)) (ContinuousMap.hasCoeToFun.{u2, max u1 u3} A (forall (i : I), (fun (i : I) => X i) i) _inst_5 (Pi.topologicalSpace.{u1, u3} I (fun (i : I) => (fun (i : I) => X i) i) (fun (a : I) => (fun (i : I) => _inst_6 i) a))) (ContinuousMap.pi.{u1, u2, u3} I A (fun (i : I) => X i) _inst_5 (fun (i : I) => _inst_6 i) f) a) (fun (i : I) => coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (ContinuousMap.{u2, u3} A (X i) _inst_5 (_inst_6 i)) (fun (_x : ContinuousMap.{u2, u3} A (X i) _inst_5 (_inst_6 i)) => A -> (X i)) (ContinuousMap.hasCoeToFun.{u2, u3} A (X i) _inst_5 (_inst_6 i)) (f i) a)
but is expected to have type
  forall {I : Type.{u1}} {A : Type.{u3}} {X : I -> Type.{u2}} [_inst_5 : TopologicalSpace.{u3} A] [_inst_6 : forall (i : I), TopologicalSpace.{u2} (X i)] (f : forall (i : I), ContinuousMap.{u3, u2} A (X i) _inst_5 (_inst_6 i)) (a : A), Eq.{max (succ u1) (succ u2)} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : A) => forall (i : I), X i) a) (FunLike.coe.{max (max (succ u1) (succ u3)) (succ u2), succ u3, max (succ u1) (succ u2)} (ContinuousMap.{u3, max u1 u2} A (forall (i : I), X i) _inst_5 (Pi.topologicalSpace.{u1, u2} I (fun (i : I) => X i) (fun (a : I) => _inst_6 a))) A (fun (_x : A) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : A) => forall (i : I), X i) _x) (ContinuousMapClass.toFunLike.{max (max u1 u3) u2, u3, max u1 u2} (ContinuousMap.{u3, max u1 u2} A (forall (i : I), X i) _inst_5 (Pi.topologicalSpace.{u1, u2} I (fun (i : I) => X i) (fun (a : I) => _inst_6 a))) A (forall (i : I), X i) _inst_5 (Pi.topologicalSpace.{u1, u2} I (fun (i : I) => X i) (fun (a : I) => _inst_6 a)) (ContinuousMap.instContinuousMapClassContinuousMap.{u3, max u1 u2} A (forall (i : I), X i) _inst_5 (Pi.topologicalSpace.{u1, u2} I (fun (i : I) => X i) (fun (a : I) => _inst_6 a)))) (ContinuousMap.pi.{u1, u3, u2} I A (fun (i : I) => X i) _inst_5 (fun (i : I) => _inst_6 i) f) a) (fun (i : I) => FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (ContinuousMap.{u3, u2} A (X i) _inst_5 (_inst_6 i)) A (fun (_x : A) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : A) => X i) _x) (ContinuousMapClass.toFunLike.{max u3 u2, u3, u2} (ContinuousMap.{u3, u2} A (X i) _inst_5 (_inst_6 i)) A (X i) _inst_5 (_inst_6 i) (ContinuousMap.instContinuousMapClassContinuousMap.{u3, u2} A (X i) _inst_5 (_inst_6 i))) (f i) a)
Case conversion may be inaccurate. Consider using '#align continuous_map.pi_eval ContinuousMap.pi_evalₓ'. -/
@[simp]
theorem pi_eval (f : ∀ i, C(A, X i)) (a : A) : (pi f) a = fun i : I => (f i) a :=
  rfl
#align continuous_map.pi_eval ContinuousMap.pi_eval

end Pi

section Restrict

variable (s : Set α)

#print ContinuousMap.restrict /-
/-- The restriction of a continuous function `α → β` to a subset `s` of `α`. -/
def restrict (f : C(α, β)) : C(s, β) :=
  ⟨f ∘ coe⟩
#align continuous_map.restrict ContinuousMap.restrict
-/

/- warning: continuous_map.coe_restrict -> ContinuousMap.coe_restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (s : Set.{u1} α) (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} ((coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (fun (_x : ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> β) (ContinuousMap.hasCoeToFun.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (ContinuousMap.restrict.{u1, u2} α β _inst_1 _inst_2 s f)) (Function.comp.{succ u1, succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (s : Set.{u2} α) (f : ContinuousMap.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : Set.Elem.{u2} α s), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : Set.Elem.{u2} α s) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2) (Set.Elem.{u2} α s) (fun (_x : Set.Elem.{u2} α s) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : Set.Elem.{u2} α s) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2) (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2)) (ContinuousMap.restrict.{u2, u1} α β _inst_1 _inst_2 s f)) (Function.comp.{succ u2, succ u2, succ u1} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)) α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) f) (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)))
Case conversion may be inaccurate. Consider using '#align continuous_map.coe_restrict ContinuousMap.coe_restrictₓ'. -/
@[simp]
theorem coe_restrict (f : C(α, β)) : ⇑(f.restrict s) = f ∘ coe :=
  rfl
#align continuous_map.coe_restrict ContinuousMap.coe_restrict

/- warning: continuous_map.restrict_preimage -> ContinuousMap.restrictPreimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u2} β), ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f) s)) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f) s)) _inst_1) (Subtype.topologicalSpace.{u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u2} β), ContinuousMap.{u1, u2} (Set.Elem.{u1} α (Set.preimage.{u1, u2} α β (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) f) s)) (Set.Elem.{u2} β s) (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Set.preimage.{u1, u2} α β (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) f) s)) _inst_1) (instTopologicalSpaceSubtype.{u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) _inst_2)
Case conversion may be inaccurate. Consider using '#align continuous_map.restrict_preimage ContinuousMap.restrictPreimageₓ'. -/
/-- The restriction of a continuous map onto the preimage of a set. -/
@[simps]
def restrictPreimage (f : C(α, β)) (s : Set β) : C(f ⁻¹' s, s) :=
  ⟨s.restrictPreimage f, continuous_iff_continuousAt.mpr fun x => f.2.ContinuousAt.restrictPreimage⟩
#align continuous_map.restrict_preimage ContinuousMap.restrictPreimage

end Restrict

section Gluing

variable {ι : Type _} (S : ι → Set α) (φ : ∀ i : ι, C(S i, β))
  (hφ : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩)
  (hS : ∀ x : α, ∃ i, S i ∈ nhds x)

include hφ hS

/- warning: continuous_map.lift_cover -> ContinuousMap.liftCover is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {ι : Type.{u3}} (S : ι -> (Set.{u1} α)) (φ : forall (i : ι), ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) _inst_1) _inst_2), (forall (i : ι) (j : ι) (x : α) (hxi : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) (hxj : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) _inst_1) _inst_2) (fun (_x : ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) _inst_1) _inst_2) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) -> β) (ContinuousMap.hasCoeToFun.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) _inst_1) _inst_2) (φ i) (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) x hxi)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S j)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)) _inst_1) _inst_2) (fun (_x : ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S j)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)) _inst_1) _inst_2) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S j)) -> β) (ContinuousMap.hasCoeToFun.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S j)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)) _inst_1) _inst_2) (φ j) (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)) x hxj))) -> (forall (x : α), Exists.{succ u3} ι (fun (i : ι) => Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (S i) (nhds.{u1} α _inst_1 x))) -> (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {ι : Type.{u3}} (S : ι -> (Set.{u1} α)) (φ : forall (i : ι), ContinuousMap.{u1, u2} (Set.Elem.{u1} α (S i)) β (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (S i)) _inst_1) _inst_2), (forall (i : ι) (j : ι) (x : α) (hxi : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (S i)) (hxj : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (S j)), Eq.{succ u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : Set.Elem.{u1} α (S i)) => β) (Subtype.mk.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (S i)) x hxi)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} (Set.Elem.{u1} α (S i)) β (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (S i)) _inst_1) _inst_2) (Set.Elem.{u1} α (S i)) (fun (_x : Set.Elem.{u1} α (S i)) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : Set.Elem.{u1} α (S i)) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} (Set.Elem.{u1} α (S i)) β (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (S i)) _inst_1) _inst_2) (Set.Elem.{u1} α (S i)) β (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (S i)) _inst_1) _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} (Set.Elem.{u1} α (S i)) β (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (S i)) _inst_1) _inst_2)) (φ i) (Subtype.mk.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (S i)) x hxi)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} (Set.Elem.{u1} α (S j)) β (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (S j)) _inst_1) _inst_2) (Set.Elem.{u1} α (S j)) (fun (_x : Set.Elem.{u1} α (S j)) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : Set.Elem.{u1} α (S j)) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} (Set.Elem.{u1} α (S j)) β (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (S j)) _inst_1) _inst_2) (Set.Elem.{u1} α (S j)) β (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (S j)) _inst_1) _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} (Set.Elem.{u1} α (S j)) β (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (S j)) _inst_1) _inst_2)) (φ j) (Subtype.mk.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (S j)) x hxj))) -> (forall (x : α), Exists.{succ u3} ι (fun (i : ι) => Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (S i) (nhds.{u1} α _inst_1 x))) -> (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align continuous_map.lift_cover ContinuousMap.liftCoverₓ'. -/
/-- A family `φ i` of continuous maps `C(S i, β)`, where the domains `S i` contain a neighbourhood
of each point in `α` and the functions `φ i` agree pairwise on intersections, can be glued to
construct a continuous map in `C(α, β)`. -/
noncomputable def liftCover : C(α, β) :=
  by
  have H : (⋃ i, S i) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    rw [Set.mem_unionᵢ]
    obtain ⟨i, hi⟩ := hS x
    exact ⟨i, mem_of_mem_nhds hi⟩
  refine' ⟨Set.liftCover S (fun i => φ i) hφ H, continuous_subtype_nhds_cover hS _⟩
  intro i
  convert (φ i).Continuous
  ext x
  exact Set.liftCover_coe x
#align continuous_map.lift_cover ContinuousMap.liftCover

variable {S φ hφ hS}

/- warning: continuous_map.lift_cover_coe -> ContinuousMap.liftCover_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {ι : Type.{u3}} {S : ι -> (Set.{u1} α)} {φ : forall (i : ι), ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) _inst_1) _inst_2} {hφ : forall (i : ι) (j : ι) (x : α) (hxi : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) (hxj : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) _inst_1) _inst_2) (fun (_x : ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) _inst_1) _inst_2) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) -> β) (ContinuousMap.hasCoeToFun.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) _inst_1) _inst_2) (φ i) (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) x hxi)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S j)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)) _inst_1) _inst_2) (fun (_x : ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S j)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)) _inst_1) _inst_2) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S j)) -> β) (ContinuousMap.hasCoeToFun.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S j)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)) _inst_1) _inst_2) (φ j) (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)) x hxj))} {hS : forall (x : α), Exists.{succ u3} ι (fun (i : ι) => Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (S i) (nhds.{u1} α _inst_1 x))} {i : ι} (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.liftCover.{u1, u2, u3} α β _inst_1 _inst_2 ι S φ hφ hS) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)))))) x)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) _inst_1) _inst_2) (fun (_x : ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) _inst_1) _inst_2) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) -> β) (ContinuousMap.hasCoeToFun.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) _inst_1) _inst_2) (φ i) x)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] {ι : Type.{u1}} {S : ι -> (Set.{u3} α)} {φ : forall (i : ι), ContinuousMap.{u3, u2} (Set.Elem.{u3} α (S i)) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) _inst_1) _inst_2} {hφ : forall (i : ι) (j : ι) (x : α) (hxi : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) (hxj : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)), Eq.{succ u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : Set.Elem.{u3} α (S i)) => β) (Subtype.mk.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) x hxi)) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (ContinuousMap.{u3, u2} (Set.Elem.{u3} α (S i)) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) _inst_1) _inst_2) (Set.Elem.{u3} α (S i)) (fun (_x : Set.Elem.{u3} α (S i)) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : Set.Elem.{u3} α (S i)) => β) _x) (ContinuousMapClass.toFunLike.{max u3 u2, u3, u2} (ContinuousMap.{u3, u2} (Set.Elem.{u3} α (S i)) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) _inst_1) _inst_2) (Set.Elem.{u3} α (S i)) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) _inst_1) _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u3, u2} (Set.Elem.{u3} α (S i)) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) _inst_1) _inst_2)) (φ i) (Subtype.mk.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) x hxi)) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (ContinuousMap.{u3, u2} (Set.Elem.{u3} α (S j)) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)) _inst_1) _inst_2) (Set.Elem.{u3} α (S j)) (fun (_x : Set.Elem.{u3} α (S j)) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : Set.Elem.{u3} α (S j)) => β) _x) (ContinuousMapClass.toFunLike.{max u3 u2, u3, u2} (ContinuousMap.{u3, u2} (Set.Elem.{u3} α (S j)) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)) _inst_1) _inst_2) (Set.Elem.{u3} α (S j)) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)) _inst_1) _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u3, u2} (Set.Elem.{u3} α (S j)) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)) _inst_1) _inst_2)) (φ j) (Subtype.mk.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)) x hxj))} {hS : forall (x : α), Exists.{succ u1} ι (fun (i : ι) => Membership.mem.{u3, u3} (Set.{u3} α) (Filter.{u3} α) (instMembershipSetFilter.{u3} α) (S i) (nhds.{u3} α _inst_1 x))} {i : ι} (x : Set.Elem.{u3} α (S i)), Eq.{succ u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) x)) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (ContinuousMap.{u3, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u3 u2, u3, u2} (ContinuousMap.{u3, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u3, u2} α β _inst_1 _inst_2)) (ContinuousMap.liftCover.{u3, u2, u1} α β _inst_1 _inst_2 ι S φ hφ hS) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) x)) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (ContinuousMap.{u3, u2} (Set.Elem.{u3} α (S i)) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) _inst_1) _inst_2) (Set.Elem.{u3} α (S i)) (fun (_x : Set.Elem.{u3} α (S i)) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : Set.Elem.{u3} α (S i)) => β) _x) (ContinuousMapClass.toFunLike.{max u3 u2, u3, u2} (ContinuousMap.{u3, u2} (Set.Elem.{u3} α (S i)) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) _inst_1) _inst_2) (Set.Elem.{u3} α (S i)) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) _inst_1) _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u3, u2} (Set.Elem.{u3} α (S i)) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) _inst_1) _inst_2)) (φ i) x)
Case conversion may be inaccurate. Consider using '#align continuous_map.lift_cover_coe ContinuousMap.liftCover_coeₓ'. -/
@[simp]
theorem liftCover_coe {i : ι} (x : S i) : liftCover S φ hφ hS x = φ i x :=
  Set.liftCover_coe _
#align continuous_map.lift_cover_coe ContinuousMap.liftCover_coe

/- warning: continuous_map.lift_cover_restrict -> ContinuousMap.liftCover_restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {ι : Type.{u3}} {S : ι -> (Set.{u1} α)} {φ : forall (i : ι), ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) _inst_1) _inst_2} {hφ : forall (i : ι) (j : ι) (x : α) (hxi : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) (hxj : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) _inst_1) _inst_2) (fun (_x : ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) _inst_1) _inst_2) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) -> β) (ContinuousMap.hasCoeToFun.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) _inst_1) _inst_2) (φ i) (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) x hxi)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S j)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)) _inst_1) _inst_2) (fun (_x : ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S j)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)) _inst_1) _inst_2) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S j)) -> β) (ContinuousMap.hasCoeToFun.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S j)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)) _inst_1) _inst_2) (φ j) (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)) x hxj))} {hS : forall (x : α), Exists.{succ u3} ι (fun (i : ι) => Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (S i) (nhds.{u1} α _inst_1 x))} {i : ι}, Eq.{max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) _inst_1) _inst_2) (ContinuousMap.restrict.{u1, u2} α β _inst_1 _inst_2 (S i) (ContinuousMap.liftCover.{u1, u2, u3} α β _inst_1 _inst_2 ι S φ hφ hS)) (φ i)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] {ι : Type.{u1}} {S : ι -> (Set.{u3} α)} {φ : forall (i : ι), ContinuousMap.{u3, u2} (Set.Elem.{u3} α (S i)) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) _inst_1) _inst_2} {hφ : forall (i : ι) (j : ι) (x : α) (hxi : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) (hxj : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)), Eq.{succ u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : Set.Elem.{u3} α (S i)) => β) (Subtype.mk.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) x hxi)) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (ContinuousMap.{u3, u2} (Set.Elem.{u3} α (S i)) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) _inst_1) _inst_2) (Set.Elem.{u3} α (S i)) (fun (_x : Set.Elem.{u3} α (S i)) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : Set.Elem.{u3} α (S i)) => β) _x) (ContinuousMapClass.toFunLike.{max u3 u2, u3, u2} (ContinuousMap.{u3, u2} (Set.Elem.{u3} α (S i)) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) _inst_1) _inst_2) (Set.Elem.{u3} α (S i)) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) _inst_1) _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u3, u2} (Set.Elem.{u3} α (S i)) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) _inst_1) _inst_2)) (φ i) (Subtype.mk.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) x hxi)) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (ContinuousMap.{u3, u2} (Set.Elem.{u3} α (S j)) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)) _inst_1) _inst_2) (Set.Elem.{u3} α (S j)) (fun (_x : Set.Elem.{u3} α (S j)) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : Set.Elem.{u3} α (S j)) => β) _x) (ContinuousMapClass.toFunLike.{max u3 u2, u3, u2} (ContinuousMap.{u3, u2} (Set.Elem.{u3} α (S j)) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)) _inst_1) _inst_2) (Set.Elem.{u3} α (S j)) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)) _inst_1) _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u3, u2} (Set.Elem.{u3} α (S j)) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)) _inst_1) _inst_2)) (φ j) (Subtype.mk.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)) x hxj))} {hS : forall (x : α), Exists.{succ u1} ι (fun (i : ι) => Membership.mem.{u3, u3} (Set.{u3} α) (Filter.{u3} α) (instMembershipSetFilter.{u3} α) (S i) (nhds.{u3} α _inst_1 x))} {i : ι}, Eq.{max (succ u3) (succ u2)} (ContinuousMap.{u3, u2} (Set.Elem.{u3} α (S i)) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) _inst_1) _inst_2) (ContinuousMap.restrict.{u3, u2} α β _inst_1 _inst_2 (S i) (ContinuousMap.liftCover.{u3, u2, u1} α β _inst_1 _inst_2 ι S φ hφ hS)) (φ i)
Case conversion may be inaccurate. Consider using '#align continuous_map.lift_cover_restrict ContinuousMap.liftCover_restrictₓ'. -/
@[simp]
theorem liftCover_restrict {i : ι} : (liftCover S φ hφ hS).restrict (S i) = φ i :=
  ext <| liftCover_coe
#align continuous_map.lift_cover_restrict ContinuousMap.liftCover_restrict

omit hφ hS

variable (A : Set (Set α)) (F : ∀ (s : Set α) (hi : s ∈ A), C(s, β))
  (hF :
    ∀ (s) (hs : s ∈ A) (t) (ht : t ∈ A) (x : α) (hxi : x ∈ s) (hxj : x ∈ t),
      F s hs ⟨x, hxi⟩ = F t ht ⟨x, hxj⟩)
  (hA : ∀ x : α, ∃ i ∈ A, i ∈ nhds x)

include hF hA

/- warning: continuous_map.lift_cover' -> ContinuousMap.liftCover' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (A : Set.{u1} (Set.{u1} α)) (F : forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s A) -> (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2)), (forall (s : Set.{u1} α) (hs : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s A) (t : Set.{u1} α) (ht : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) t A) (x : α) (hxi : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (hxj : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (fun (_x : ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> β) (ContinuousMap.hasCoeToFun.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (F s hs) (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) x hxi)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) _inst_1) _inst_2) (fun (_x : ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) _inst_1) _inst_2) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) -> β) (ContinuousMap.hasCoeToFun.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) _inst_1) _inst_2) (F t ht) (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) x hxj))) -> (forall (x : α), Exists.{succ u1} (Set.{u1} α) (fun (i : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) i A) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) i A) => Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) i (nhds.{u1} α _inst_1 x)))) -> (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (A : Set.{u1} (Set.{u1} α)) (F : forall (s : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s A) -> (ContinuousMap.{u1, u2} (Set.Elem.{u1} α s) β (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) _inst_1) _inst_2)), (forall (s : Set.{u1} α) (hs : Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s A) (t : Set.{u1} α) (ht : Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) t A) (x : α) (hxi : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (hxj : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t), Eq.{succ u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : Set.Elem.{u1} α s) => β) (Subtype.mk.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) x hxi)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} (Set.Elem.{u1} α s) β (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) _inst_1) _inst_2) (Set.Elem.{u1} α s) (fun (_x : Set.Elem.{u1} α s) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : Set.Elem.{u1} α s) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} (Set.Elem.{u1} α s) β (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) _inst_1) _inst_2) (Set.Elem.{u1} α s) β (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) _inst_1) _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} (Set.Elem.{u1} α s) β (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) _inst_1) _inst_2)) (F s hs) (Subtype.mk.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) x hxi)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} (Set.Elem.{u1} α t) β (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) _inst_1) _inst_2) (Set.Elem.{u1} α t) (fun (_x : Set.Elem.{u1} α t) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : Set.Elem.{u1} α t) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} (Set.Elem.{u1} α t) β (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) _inst_1) _inst_2) (Set.Elem.{u1} α t) β (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) _inst_1) _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} (Set.Elem.{u1} α t) β (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) _inst_1) _inst_2)) (F t ht) (Subtype.mk.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) x hxj))) -> (forall (x : α), Exists.{succ u1} (Set.{u1} α) (fun (i : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) i A) (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) i (nhds.{u1} α _inst_1 x)))) -> (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align continuous_map.lift_cover' ContinuousMap.liftCover'ₓ'. -/
/-- A family `F s` of continuous maps `C(s, β)`, where (1) the domains `s` are taken from a set `A`
of sets in `α` which contain a neighbourhood of each point in `α` and (2) the functions `F s` agree
pairwise on intersections, can be glued to construct a continuous map in `C(α, β)`. -/
noncomputable def liftCover' : C(α, β) :=
  by
  let S : A → Set α := coe
  let F : ∀ i : A, C(i, β) := fun i => F i i.Prop
  refine' lift_cover S F (fun i j => hF i i.Prop j j.Prop) _
  intro x
  obtain ⟨s, hs, hsx⟩ := hA x
  exact ⟨⟨s, hs⟩, hsx⟩
#align continuous_map.lift_cover' ContinuousMap.liftCover'

variable {A F hF hA}

/- warning: continuous_map.lift_cover_coe' -> ContinuousMap.liftCover_coe' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {A : Set.{u1} (Set.{u1} α)} {F : forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s A) -> (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2)} {hF : forall (s : Set.{u1} α) (hs : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s A) (t : Set.{u1} α) (ht : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) t A) (x : α) (hxi : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (hxj : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (fun (_x : ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> β) (ContinuousMap.hasCoeToFun.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (F s hs) (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) x hxi)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) _inst_1) _inst_2) (fun (_x : ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) _inst_1) _inst_2) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) -> β) (ContinuousMap.hasCoeToFun.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) _inst_1) _inst_2) (F t ht) (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) x hxj))} {hA : forall (x : α), Exists.{succ u1} (Set.{u1} α) (fun (i : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) i A) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) i A) => Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) i (nhds.{u1} α _inst_1 x)))} {s : Set.{u1} α} {hs : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s A} (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.liftCover'.{u1, u2} α β _inst_1 _inst_2 A F hF hA) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) x)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (fun (_x : ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> β) (ContinuousMap.hasCoeToFun.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (F s hs) x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {A : Set.{u2} (Set.{u2} α)} {F : forall (s : Set.{u2} α), (Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) s A) -> (ContinuousMap.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2)} {hF : forall (s : Set.{u2} α) (hs : Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) s A) (t : Set.{u2} α) (ht : Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) t A) (x : α) (hxi : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (hxj : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : Set.Elem.{u2} α s) => β) (Subtype.mk.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x hxi)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2) (Set.Elem.{u2} α s) (fun (_x : Set.Elem.{u2} α s) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : Set.Elem.{u2} α s) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2) (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2)) (F s hs) (Subtype.mk.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x hxi)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} (Set.Elem.{u2} α t) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t) _inst_1) _inst_2) (Set.Elem.{u2} α t) (fun (_x : Set.Elem.{u2} α t) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : Set.Elem.{u2} α t) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} (Set.Elem.{u2} α t) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t) _inst_1) _inst_2) (Set.Elem.{u2} α t) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t) _inst_1) _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} (Set.Elem.{u2} α t) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t) _inst_1) _inst_2)) (F t ht) (Subtype.mk.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t) x hxj))} {hA : forall (x : α), Exists.{succ u2} (Set.{u2} α) (fun (i : Set.{u2} α) => And (Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) i A) (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) i (nhds.{u2} α _inst_1 x)))} {s : Set.{u2} α} {hs : Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) s A} (x : Set.Elem.{u2} α s), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (ContinuousMap.liftCover'.{u2, u1} α β _inst_1 _inst_2 A F hF hA) (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2) (Set.Elem.{u2} α s) (fun (_x : Set.Elem.{u2} α s) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : Set.Elem.{u2} α s) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2) (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2)) (F s hs) x)
Case conversion may be inaccurate. Consider using '#align continuous_map.lift_cover_coe' ContinuousMap.liftCover_coe'ₓ'. -/
@[simp]
theorem liftCover_coe' {s : Set α} {hs : s ∈ A} (x : s) : liftCover' A F hF hA x = F s hs x :=
  let x' : (coe : A → Set α) ⟨s, hs⟩ := x
  liftCover_coe x'
#align continuous_map.lift_cover_coe' ContinuousMap.liftCover_coe'

/- warning: continuous_map.lift_cover_restrict' -> ContinuousMap.liftCover_restrict' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {A : Set.{u1} (Set.{u1} α)} {F : forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s A) -> (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2)} {hF : forall (s : Set.{u1} α) (hs : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s A) (t : Set.{u1} α) (ht : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) t A) (x : α) (hxi : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (hxj : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (fun (_x : ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> β) (ContinuousMap.hasCoeToFun.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (F s hs) (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) x hxi)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) _inst_1) _inst_2) (fun (_x : ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) _inst_1) _inst_2) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) -> β) (ContinuousMap.hasCoeToFun.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) _inst_1) _inst_2) (F t ht) (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) x hxj))} {hA : forall (x : α), Exists.{succ u1} (Set.{u1} α) (fun (i : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) i A) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) i A) => Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) i (nhds.{u1} α _inst_1 x)))} {s : Set.{u1} α} {hs : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s A}, Eq.{max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (ContinuousMap.restrict.{u1, u2} α β _inst_1 _inst_2 s (ContinuousMap.liftCover'.{u1, u2} α β _inst_1 _inst_2 A F hF hA)) (F s hs)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {A : Set.{u2} (Set.{u2} α)} {F : forall (s : Set.{u2} α), (Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) s A) -> (ContinuousMap.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2)} {hF : forall (s : Set.{u2} α) (hs : Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) s A) (t : Set.{u2} α) (ht : Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) t A) (x : α) (hxi : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (hxj : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : Set.Elem.{u2} α s) => β) (Subtype.mk.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x hxi)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2) (Set.Elem.{u2} α s) (fun (_x : Set.Elem.{u2} α s) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : Set.Elem.{u2} α s) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2) (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2)) (F s hs) (Subtype.mk.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x hxi)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} (Set.Elem.{u2} α t) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t) _inst_1) _inst_2) (Set.Elem.{u2} α t) (fun (_x : Set.Elem.{u2} α t) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.669 : Set.Elem.{u2} α t) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} (Set.Elem.{u2} α t) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t) _inst_1) _inst_2) (Set.Elem.{u2} α t) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t) _inst_1) _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} (Set.Elem.{u2} α t) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t) _inst_1) _inst_2)) (F t ht) (Subtype.mk.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t) x hxj))} {hA : forall (x : α), Exists.{succ u2} (Set.{u2} α) (fun (i : Set.{u2} α) => And (Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) i A) (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) i (nhds.{u2} α _inst_1 x)))} {s : Set.{u2} α} {hs : Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) s A}, Eq.{max (succ u2) (succ u1)} (ContinuousMap.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2) (ContinuousMap.restrict.{u2, u1} α β _inst_1 _inst_2 s (ContinuousMap.liftCover'.{u2, u1} α β _inst_1 _inst_2 A F hF hA)) (F s hs)
Case conversion may be inaccurate. Consider using '#align continuous_map.lift_cover_restrict' ContinuousMap.liftCover_restrict'ₓ'. -/
@[simp]
theorem liftCover_restrict' {s : Set α} {hs : s ∈ A} : (liftCover' A F hF hA).restrict s = F s hs :=
  ext <| liftCover_coe'
#align continuous_map.lift_cover_restrict' ContinuousMap.liftCover_restrict'

end Gluing

end ContinuousMap

namespace Homeomorph

variable {α β γ : Type _} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

variable (f : α ≃ₜ β) (g : β ≃ₜ γ)

#print Homeomorph.toContinuousMap /-
/-- The forward direction of a homeomorphism, as a bundled continuous map. -/
@[simps]
def toContinuousMap (e : α ≃ₜ β) : C(α, β) :=
  ⟨e⟩
#align homeomorph.to_continuous_map Homeomorph.toContinuousMap
-/

/-- `homeomorph.to_continuous_map` as a coercion. -/
instance : Coe (α ≃ₜ β) C(α, β) :=
  ⟨Homeomorph.toContinuousMap⟩

/- warning: homeomorph.to_continuous_map_as_coe clashes with [anonymous] -> [anonymous]
warning: homeomorph.to_continuous_map_as_coe -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (Homeomorph.toContinuousMap.{u1, u2} α β _inst_1 _inst_2 f) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{max (succ u1) (succ u2), max (succ u1) (succ u2)} a b] => self.0) (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (HasLiftT.mk.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (CoeTCₓ.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (coeBase.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (Homeomorph.ContinuousMap.hasCoe.{u1, u2} α β _inst_1 _inst_2)))) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}}, (Nat -> α -> β) -> Nat -> (List.{u1} α) -> (List.{u2} β)
Case conversion may be inaccurate. Consider using '#align homeomorph.to_continuous_map_as_coe [anonymous]ₓ'. -/
theorem [anonymous] : f.toContinuousMap = f :=
  rfl
#align homeomorph.to_continuous_map_as_coe [anonymous]

#print Homeomorph.coe_refl /-
@[simp]
theorem coe_refl : (Homeomorph.refl α : C(α, α)) = ContinuousMap.id α :=
  rfl
#align homeomorph.coe_refl Homeomorph.coe_refl
-/

/- warning: homeomorph.coe_trans -> Homeomorph.coe_trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (f : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (g : Homeomorph.{u2, u3} β γ _inst_2 _inst_3), Eq.{max (succ u1) (succ u3)} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) ((fun (a : Sort.{max (succ u1) (succ u3)}) (b : Sort.{max (succ u1) (succ u3)}) [self : HasLiftT.{max (succ u1) (succ u3), max (succ u1) (succ u3)} a b] => self.0) (Homeomorph.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (HasLiftT.mk.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (Homeomorph.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (CoeTCₓ.coe.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (Homeomorph.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (coeBase.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (Homeomorph.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (Homeomorph.ContinuousMap.hasCoe.{u1, u3} α γ _inst_1 _inst_3)))) (Homeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g)) (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 ((fun (a : Sort.{max (succ u2) (succ u3)}) (b : Sort.{max (succ u2) (succ u3)}) [self : HasLiftT.{max (succ u2) (succ u3), max (succ u2) (succ u3)} a b] => self.0) (Homeomorph.{u2, u3} β γ _inst_2 _inst_3) (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (HasLiftT.mk.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (Homeomorph.{u2, u3} β γ _inst_2 _inst_3) (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (CoeTCₓ.coe.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (Homeomorph.{u2, u3} β γ _inst_2 _inst_3) (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (coeBase.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (Homeomorph.{u2, u3} β γ _inst_2 _inst_3) (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (Homeomorph.ContinuousMap.hasCoe.{u2, u3} β γ _inst_2 _inst_3)))) g) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{max (succ u1) (succ u2), max (succ u1) (succ u2)} a b] => self.0) (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (HasLiftT.mk.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (CoeTCₓ.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (coeBase.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (Homeomorph.ContinuousMap.hasCoe.{u1, u2} α β _inst_1 _inst_2)))) f))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.{u2} γ] (f : Homeomorph.{u3, u1} α β _inst_1 _inst_2) (g : Homeomorph.{u1, u2} β γ _inst_2 _inst_3), Eq.{max (succ u3) (succ u2)} (ContinuousMap.{u3, u2} α γ _inst_1 _inst_3) (Homeomorph.toContinuousMap.{u3, u2} α γ _inst_1 _inst_3 (Homeomorph.trans.{u3, u1, u2} α β γ _inst_1 _inst_2 _inst_3 f g)) (ContinuousMap.comp.{u3, u1, u2} α β γ _inst_1 _inst_2 _inst_3 (Homeomorph.toContinuousMap.{u1, u2} β γ _inst_2 _inst_3 g) (Homeomorph.toContinuousMap.{u3, u1} α β _inst_1 _inst_2 f))
Case conversion may be inaccurate. Consider using '#align homeomorph.coe_trans Homeomorph.coe_transₓ'. -/
@[simp]
theorem coe_trans : (f.trans g : C(α, γ)) = (g : C(β, γ)).comp f :=
  rfl
#align homeomorph.coe_trans Homeomorph.coe_trans

/- warning: homeomorph.symm_comp_to_continuous_map -> Homeomorph.symm_comp_to_continuousMap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{succ u1} (ContinuousMap.{u1, u1} α α _inst_1 _inst_1) (ContinuousMap.comp.{u1, u2, u1} α β α _inst_1 _inst_2 _inst_1 ((fun (a : Sort.{max (succ u2) (succ u1)}) (b : Sort.{max (succ u2) (succ u1)}) [self : HasLiftT.{max (succ u2) (succ u1), max (succ u2) (succ u1)} a b] => self.0) (Homeomorph.{u2, u1} β α _inst_2 _inst_1) (ContinuousMap.{u2, u1} β α _inst_2 _inst_1) (HasLiftT.mk.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Homeomorph.{u2, u1} β α _inst_2 _inst_1) (ContinuousMap.{u2, u1} β α _inst_2 _inst_1) (CoeTCₓ.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Homeomorph.{u2, u1} β α _inst_2 _inst_1) (ContinuousMap.{u2, u1} β α _inst_2 _inst_1) (coeBase.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Homeomorph.{u2, u1} β α _inst_2 _inst_1) (ContinuousMap.{u2, u1} β α _inst_2 _inst_1) (Homeomorph.ContinuousMap.hasCoe.{u2, u1} β α _inst_2 _inst_1)))) (Homeomorph.symm.{u1, u2} α β _inst_1 _inst_2 f)) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{max (succ u1) (succ u2), max (succ u1) (succ u2)} a b] => self.0) (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (HasLiftT.mk.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (CoeTCₓ.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (coeBase.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (Homeomorph.ContinuousMap.hasCoe.{u1, u2} α β _inst_1 _inst_2)))) f)) (ContinuousMap.id.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : Homeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{succ u2} (ContinuousMap.{u2, u2} α α _inst_1 _inst_1) (ContinuousMap.comp.{u2, u1, u2} α β α _inst_1 _inst_2 _inst_1 (Homeomorph.toContinuousMap.{u1, u2} β α _inst_2 _inst_1 (Homeomorph.symm.{u2, u1} α β _inst_1 _inst_2 f)) (Homeomorph.toContinuousMap.{u2, u1} α β _inst_1 _inst_2 f)) (ContinuousMap.id.{u2} α _inst_1)
Case conversion may be inaccurate. Consider using '#align homeomorph.symm_comp_to_continuous_map Homeomorph.symm_comp_to_continuousMapₓ'. -/
/-- Left inverse to a continuous map from a homeomorphism, mirroring `equiv.symm_comp_self`. -/
@[simp]
theorem symm_comp_to_continuousMap : (f.symm : C(β, α)).comp (f : C(α, β)) = ContinuousMap.id α :=
  by rw [← coeTrans, self_trans_symm, coe_refl]
#align homeomorph.symm_comp_to_continuous_map Homeomorph.symm_comp_to_continuousMap

#print Homeomorph.to_continuousMap_comp_symm /-
/-- Right inverse to a continuous map from a homeomorphism, mirroring `equiv.self_comp_symm`. -/
@[simp]
theorem to_continuousMap_comp_symm : (f : C(α, β)).comp (f.symm : C(β, α)) = ContinuousMap.id β :=
  by rw [← coeTrans, symm_trans_self, coe_refl]
#align homeomorph.to_continuous_map_comp_symm Homeomorph.to_continuousMap_comp_symm
-/

end Homeomorph

