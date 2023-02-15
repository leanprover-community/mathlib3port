/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module topology.hom.open
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.ContinuousFunction.Basic

/-!
# Continuous open maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines bundled continuous open maps.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `continuous_open_map`: Continuous open maps.

## Typeclasses

* `continuous_open_map_class`
-/


open Function

variable {F α β γ δ : Type _}

#print ContinuousOpenMap /-
/-- The type of continuous open maps from `α` to `β`, aka Priestley homomorphisms. -/
structure ContinuousOpenMap (α β : Type _) [TopologicalSpace α] [TopologicalSpace β] extends
  ContinuousMap α β where
  map_open' : IsOpenMap to_fun
#align continuous_open_map ContinuousOpenMap
-/

-- mathport name: «expr →CO »
infixr:25 " →CO " => ContinuousOpenMap

section

#print ContinuousOpenMapClass /-
/-- `continuous_open_map_class F α β` states that `F` is a type of continuous open maps.

You should extend this class when you extend `continuous_open_map`. -/
class ContinuousOpenMapClass (F : Type _) (α β : outParam <| Type _) [TopologicalSpace α]
  [TopologicalSpace β] extends ContinuousMapClass F α β where
  map_open (f : F) : IsOpenMap f
#align continuous_open_map_class ContinuousOpenMapClass
-/

end

export ContinuousOpenMapClass (map_open)

instance [TopologicalSpace α] [TopologicalSpace β] [ContinuousOpenMapClass F α β] :
    CoeTC F (α →CO β) :=
  ⟨fun f => ⟨f, map_open f⟩⟩

/-! ### Continuous open maps -/


namespace ContinuousOpenMap

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

instance : ContinuousOpenMapClass (α →CO β) α β
    where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
  map_continuous f := f.continuous_toFun
  map_open f := f.map_open'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (α →CO β) fun _ => α → β :=
  FunLike.hasCoeToFun

/- warning: continuous_open_map.to_fun_eq_coe -> ContinuousOpenMap.toFun_eq_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2}, Eq.{max (succ u1) (succ u2)} (α -> β) (ContinuousMap.toFun.{u1, u2} α β _inst_1 _inst_2 (ContinuousOpenMap.toContinuousMap.{u1, u2} α β _inst_1 _inst_2 f)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousOpenMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2}, Eq.{max (succ u2) (succ u1)} (α -> β) (ContinuousMap.toFun.{u2, u1} α β _inst_1 _inst_2 (ContinuousOpenMap.toContinuousMap.{u2, u1} α β _inst_1 _inst_2 f)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousOpenMapClass.toContinuousMapClass.{max u2 u1, u2, u1} (ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousOpenMap.instContinuousOpenMapClassContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2))) f)
Case conversion may be inaccurate. Consider using '#align continuous_open_map.to_fun_eq_coe ContinuousOpenMap.toFun_eq_coeₓ'. -/
@[simp]
theorem toFun_eq_coe {f : α →CO β} : f.toFun = (f : α → β) :=
  rfl
#align continuous_open_map.to_fun_eq_coe ContinuousOpenMap.toFun_eq_coe

/- warning: continuous_open_map.ext -> ContinuousOpenMap.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2} {g : ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2}, (forall (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousOpenMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousOpenMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g a)) -> (Eq.{max (succ u1) (succ u2)} (ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2} {g : ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2}, (forall (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousOpenMapClass.toContinuousMapClass.{max u2 u1, u2, u1} (ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousOpenMap.instContinuousOpenMapClassContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2))) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousOpenMapClass.toContinuousMapClass.{max u2 u1, u2, u1} (ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousOpenMap.instContinuousOpenMapClassContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2))) g a)) -> (Eq.{max (succ u2) (succ u1)} (ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align continuous_open_map.ext ContinuousOpenMap.extₓ'. -/
@[ext]
theorem ext {f g : α →CO β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align continuous_open_map.ext ContinuousOpenMap.ext

/- warning: continuous_open_map.copy -> ContinuousOpenMap.copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousOpenMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)) -> (ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousOpenMapClass.toContinuousMapClass.{max u1 u2, u1, u2} (ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousOpenMap.instContinuousOpenMapClassContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2))) f)) -> (ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align continuous_open_map.copy ContinuousOpenMap.copyₓ'. -/
/-- Copy of a `continuous_open_map` with a new `continuous_map` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : α →CO β) (f' : α → β) (h : f' = f) : α →CO β :=
  ⟨f.toContinuousMap.copy f' <| h, h.symm.subst f.map_open'⟩
#align continuous_open_map.copy ContinuousOpenMap.copy

/- warning: continuous_open_map.coe_copy -> ContinuousOpenMap.coe_copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousOpenMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousOpenMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (ContinuousOpenMap.copy.{u1, u2} α β _inst_1 _inst_2 f f' h)) f'
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousOpenMapClass.toContinuousMapClass.{max u2 u1, u2, u1} (ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousOpenMap.instContinuousOpenMapClassContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2))) f)), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousOpenMapClass.toContinuousMapClass.{max u2 u1, u2, u1} (ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousOpenMap.instContinuousOpenMapClassContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2))) (ContinuousOpenMap.copy.{u2, u1} α β _inst_1 _inst_2 f f' h)) f'
Case conversion may be inaccurate. Consider using '#align continuous_open_map.coe_copy ContinuousOpenMap.coe_copyₓ'. -/
@[simp]
theorem coe_copy (f : α →CO β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align continuous_open_map.coe_copy ContinuousOpenMap.coe_copy

/- warning: continuous_open_map.copy_eq -> ContinuousOpenMap.copy_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousOpenMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)), Eq.{max (succ u1) (succ u2)} (ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousOpenMap.copy.{u1, u2} α β _inst_1 _inst_2 f f' h) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousOpenMapClass.toContinuousMapClass.{max u2 u1, u2, u1} (ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousOpenMap.instContinuousOpenMapClassContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2))) f)), Eq.{max (succ u2) (succ u1)} (ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2) (ContinuousOpenMap.copy.{u2, u1} α β _inst_1 _inst_2 f f' h) f
Case conversion may be inaccurate. Consider using '#align continuous_open_map.copy_eq ContinuousOpenMap.copy_eqₓ'. -/
theorem copy_eq (f : α →CO β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align continuous_open_map.copy_eq ContinuousOpenMap.copy_eq

variable (α)

#print ContinuousOpenMap.id /-
/-- `id` as a `continuous_open_map`. -/
protected def id : α →CO α :=
  ⟨ContinuousMap.id _, IsOpenMap.id⟩
#align continuous_open_map.id ContinuousOpenMap.id
-/

instance : Inhabited (α →CO α) :=
  ⟨ContinuousOpenMap.id _⟩

/- warning: continuous_open_map.coe_id -> ContinuousOpenMap.coe_id is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} α], Eq.{succ u1} (α -> α) (coeFn.{succ u1, succ u1} (ContinuousOpenMap.{u1, u1} α α _inst_1 _inst_1) (fun (_x : ContinuousOpenMap.{u1, u1} α α _inst_1 _inst_1) => α -> α) (ContinuousOpenMap.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (ContinuousOpenMap.id.{u1} α _inst_1)) (id.{succ u1} α)
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} α], Eq.{succ u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => α) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (ContinuousOpenMap.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => α) _x) (ContinuousMapClass.toFunLike.{u1, u1, u1} (ContinuousOpenMap.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (ContinuousOpenMapClass.toContinuousMapClass.{u1, u1, u1} (ContinuousOpenMap.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (ContinuousOpenMap.instContinuousOpenMapClassContinuousOpenMap.{u1, u1} α α _inst_1 _inst_1))) (ContinuousOpenMap.id.{u1} α _inst_1)) (id.{succ u1} α)
Case conversion may be inaccurate. Consider using '#align continuous_open_map.coe_id ContinuousOpenMap.coe_idₓ'. -/
@[simp]
theorem coe_id : ⇑(ContinuousOpenMap.id α) = id :=
  rfl
#align continuous_open_map.coe_id ContinuousOpenMap.coe_id

variable {α}

/- warning: continuous_open_map.id_apply -> ContinuousOpenMap.id_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (ContinuousOpenMap.{u1, u1} α α _inst_1 _inst_1) (fun (_x : ContinuousOpenMap.{u1, u1} α α _inst_1 _inst_1) => α -> α) (ContinuousOpenMap.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (ContinuousOpenMap.id.{u1} α _inst_1) a) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (ContinuousOpenMap.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => α) _x) (ContinuousMapClass.toFunLike.{u1, u1, u1} (ContinuousOpenMap.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (ContinuousOpenMapClass.toContinuousMapClass.{u1, u1, u1} (ContinuousOpenMap.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (ContinuousOpenMap.instContinuousOpenMapClassContinuousOpenMap.{u1, u1} α α _inst_1 _inst_1))) (ContinuousOpenMap.id.{u1} α _inst_1) a) a
Case conversion may be inaccurate. Consider using '#align continuous_open_map.id_apply ContinuousOpenMap.id_applyₓ'. -/
@[simp]
theorem id_apply (a : α) : ContinuousOpenMap.id α a = a :=
  rfl
#align continuous_open_map.id_apply ContinuousOpenMap.id_apply

#print ContinuousOpenMap.comp /-
/-- Composition of `continuous_open_map`s as a `continuous_open_map`. -/
def comp (f : β →CO γ) (g : α →CO β) : ContinuousOpenMap α γ :=
  ⟨f.toContinuousMap.comp g.toContinuousMap, f.map_open'.comp g.map_open'⟩
#align continuous_open_map.comp ContinuousOpenMap.comp
-/

/- warning: continuous_open_map.coe_comp -> ContinuousOpenMap.coe_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (f : ContinuousOpenMap.{u2, u3} β γ _inst_2 _inst_3) (g : ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} ((fun (_x : ContinuousOpenMap.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (ContinuousOpenMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g)) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (ContinuousOpenMap.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : ContinuousOpenMap.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (ContinuousOpenMap.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (ContinuousOpenMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g)) (Function.comp.{succ u1, succ u2, succ u3} α β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (ContinuousOpenMap.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : ContinuousOpenMap.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (ContinuousOpenMap.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousOpenMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] (f : ContinuousOpenMap.{u3, u2} β γ _inst_2 _inst_3) (g : ContinuousOpenMap.{u1, u3} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (forall (a : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => γ) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousOpenMap.{u1, u2} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => γ) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousOpenMap.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (ContinuousOpenMapClass.toContinuousMapClass.{max u1 u2, u1, u2} (ContinuousOpenMap.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (ContinuousOpenMap.instContinuousOpenMapClassContinuousOpenMap.{u1, u2} α γ _inst_1 _inst_3))) (ContinuousOpenMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g)) (Function.comp.{succ u1, succ u3, succ u2} α β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (ContinuousOpenMap.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : β) => γ) _x) (ContinuousMapClass.toFunLike.{max u3 u2, u3, u2} (ContinuousOpenMap.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (ContinuousOpenMapClass.toContinuousMapClass.{max u3 u2, u3, u2} (ContinuousOpenMap.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (ContinuousOpenMap.instContinuousOpenMapClassContinuousOpenMap.{u3, u2} β γ _inst_2 _inst_3))) f) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (ContinuousOpenMap.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u3, u1, u3} (ContinuousOpenMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousOpenMapClass.toContinuousMapClass.{max u1 u3, u1, u3} (ContinuousOpenMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousOpenMap.instContinuousOpenMapClassContinuousOpenMap.{u1, u3} α β _inst_1 _inst_2))) g))
Case conversion may be inaccurate. Consider using '#align continuous_open_map.coe_comp ContinuousOpenMap.coe_compₓ'. -/
@[simp]
theorem coe_comp (f : β →CO γ) (g : α →CO β) : (f.comp g : α → γ) = f ∘ g :=
  rfl
#align continuous_open_map.coe_comp ContinuousOpenMap.coe_comp

/- warning: continuous_open_map.comp_apply -> ContinuousOpenMap.comp_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (f : ContinuousOpenMap.{u2, u3} β γ _inst_2 _inst_3) (g : ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) (a : α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (ContinuousOpenMap.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : ContinuousOpenMap.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (ContinuousOpenMap.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (ContinuousOpenMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g) a) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (ContinuousOpenMap.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : ContinuousOpenMap.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (ContinuousOpenMap.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousOpenMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] (f : ContinuousOpenMap.{u3, u2} β γ _inst_2 _inst_3) (g : ContinuousOpenMap.{u1, u3} α β _inst_1 _inst_2) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => γ) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousOpenMap.{u1, u2} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => γ) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousOpenMap.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (ContinuousOpenMapClass.toContinuousMapClass.{max u1 u2, u1, u2} (ContinuousOpenMap.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (ContinuousOpenMap.instContinuousOpenMapClassContinuousOpenMap.{u1, u2} α γ _inst_1 _inst_3))) (ContinuousOpenMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g) a) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (ContinuousOpenMap.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : β) => γ) _x) (ContinuousMapClass.toFunLike.{max u3 u2, u3, u2} (ContinuousOpenMap.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (ContinuousOpenMapClass.toContinuousMapClass.{max u3 u2, u3, u2} (ContinuousOpenMap.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (ContinuousOpenMap.instContinuousOpenMapClassContinuousOpenMap.{u3, u2} β γ _inst_2 _inst_3))) f (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (ContinuousOpenMap.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u3, u1, u3} (ContinuousOpenMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousOpenMapClass.toContinuousMapClass.{max u1 u3, u1, u3} (ContinuousOpenMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousOpenMap.instContinuousOpenMapClassContinuousOpenMap.{u1, u3} α β _inst_1 _inst_2))) g a))
Case conversion may be inaccurate. Consider using '#align continuous_open_map.comp_apply ContinuousOpenMap.comp_applyₓ'. -/
@[simp]
theorem comp_apply (f : β →CO γ) (g : α →CO β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align continuous_open_map.comp_apply ContinuousOpenMap.comp_apply

/- warning: continuous_open_map.comp_assoc -> ContinuousOpenMap.comp_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] (f : ContinuousOpenMap.{u3, u4} γ δ _inst_3 _inst_4) (g : ContinuousOpenMap.{u2, u3} β γ _inst_2 _inst_3) (h : ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u4)} (ContinuousOpenMap.{u1, u4} α δ _inst_1 _inst_4) (ContinuousOpenMap.comp.{u1, u2, u4} α β δ _inst_1 _inst_2 _inst_4 (ContinuousOpenMap.comp.{u2, u3, u4} β γ δ _inst_2 _inst_3 _inst_4 f g) h) (ContinuousOpenMap.comp.{u1, u3, u4} α γ δ _inst_1 _inst_3 _inst_4 f (ContinuousOpenMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g h))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u4}} {δ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u4} γ] [_inst_4 : TopologicalSpace.{u3} δ] (f : ContinuousOpenMap.{u4, u3} γ δ _inst_3 _inst_4) (g : ContinuousOpenMap.{u2, u4} β γ _inst_2 _inst_3) (h : ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (ContinuousOpenMap.{u1, u3} α δ _inst_1 _inst_4) (ContinuousOpenMap.comp.{u1, u2, u3} α β δ _inst_1 _inst_2 _inst_4 (ContinuousOpenMap.comp.{u2, u4, u3} β γ δ _inst_2 _inst_3 _inst_4 f g) h) (ContinuousOpenMap.comp.{u1, u4, u3} α γ δ _inst_1 _inst_3 _inst_4 f (ContinuousOpenMap.comp.{u1, u2, u4} α β γ _inst_1 _inst_2 _inst_3 g h))
Case conversion may be inaccurate. Consider using '#align continuous_open_map.comp_assoc ContinuousOpenMap.comp_assocₓ'. -/
@[simp]
theorem comp_assoc (f : γ →CO δ) (g : β →CO γ) (h : α →CO β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align continuous_open_map.comp_assoc ContinuousOpenMap.comp_assoc

/- warning: continuous_open_map.comp_id -> ContinuousOpenMap.comp_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousOpenMap.comp.{u1, u1, u2} α α β _inst_1 _inst_1 _inst_2 f (ContinuousOpenMap.id.{u1} α _inst_1)) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2) (ContinuousOpenMap.comp.{u2, u2, u1} α α β _inst_1 _inst_1 _inst_2 f (ContinuousOpenMap.id.{u2} α _inst_1)) f
Case conversion may be inaccurate. Consider using '#align continuous_open_map.comp_id ContinuousOpenMap.comp_idₓ'. -/
@[simp]
theorem comp_id (f : α →CO β) : f.comp (ContinuousOpenMap.id α) = f :=
  ext fun a => rfl
#align continuous_open_map.comp_id ContinuousOpenMap.comp_id

/- warning: continuous_open_map.id_comp -> ContinuousOpenMap.id_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousOpenMap.comp.{u1, u2, u2} α β β _inst_1 _inst_2 _inst_2 (ContinuousOpenMap.id.{u2} β _inst_2) f) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (ContinuousOpenMap.{u2, u1} α β _inst_1 _inst_2) (ContinuousOpenMap.comp.{u2, u1, u1} α β β _inst_1 _inst_2 _inst_2 (ContinuousOpenMap.id.{u1} β _inst_2) f) f
Case conversion may be inaccurate. Consider using '#align continuous_open_map.id_comp ContinuousOpenMap.id_compₓ'. -/
@[simp]
theorem id_comp (f : α →CO β) : (ContinuousOpenMap.id β).comp f = f :=
  ext fun a => rfl
#align continuous_open_map.id_comp ContinuousOpenMap.id_comp

/- warning: continuous_open_map.cancel_right -> ContinuousOpenMap.cancel_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {g₁ : ContinuousOpenMap.{u2, u3} β γ _inst_2 _inst_3} {g₂ : ContinuousOpenMap.{u2, u3} β γ _inst_2 _inst_3} {f : ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousOpenMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)) -> (Iff (Eq.{max (succ u1) (succ u3)} (ContinuousOpenMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousOpenMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g₁ f) (ContinuousOpenMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u2) (succ u3)} (ContinuousOpenMap.{u2, u3} β γ _inst_2 _inst_3) g₁ g₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] {g₁ : ContinuousOpenMap.{u3, u2} β γ _inst_2 _inst_3} {g₂ : ContinuousOpenMap.{u3, u2} β γ _inst_2 _inst_3} {f : ContinuousOpenMap.{u1, u3} α β _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u3} α β (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (ContinuousOpenMap.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u3, u1, u3} (ContinuousOpenMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousOpenMapClass.toContinuousMapClass.{max u1 u3, u1, u3} (ContinuousOpenMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousOpenMap.instContinuousOpenMapClassContinuousOpenMap.{u1, u3} α β _inst_1 _inst_2))) f)) -> (Iff (Eq.{max (succ u1) (succ u2)} (ContinuousOpenMap.{u1, u2} α γ _inst_1 _inst_3) (ContinuousOpenMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g₁ f) (ContinuousOpenMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u3) (succ u2)} (ContinuousOpenMap.{u3, u2} β γ _inst_2 _inst_3) g₁ g₂))
Case conversion may be inaccurate. Consider using '#align continuous_open_map.cancel_right ContinuousOpenMap.cancel_rightₓ'. -/
theorem cancel_right {g₁ g₂ : β →CO γ} {f : α →CO β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align continuous_open_map.cancel_right ContinuousOpenMap.cancel_right

/- warning: continuous_open_map.cancel_left -> ContinuousOpenMap.cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {g : ContinuousOpenMap.{u2, u3} β γ _inst_2 _inst_3} {f₁ : ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2} {f₂ : ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u3} β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (ContinuousOpenMap.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : ContinuousOpenMap.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (ContinuousOpenMap.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) g)) -> (Iff (Eq.{max (succ u1) (succ u3)} (ContinuousOpenMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousOpenMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f₁) (ContinuousOpenMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u1) (succ u2)} (ContinuousOpenMap.{u1, u2} α β _inst_1 _inst_2) f₁ f₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] {g : ContinuousOpenMap.{u3, u2} β γ _inst_2 _inst_3} {f₁ : ContinuousOpenMap.{u1, u3} α β _inst_1 _inst_2} {f₂ : ContinuousOpenMap.{u1, u3} α β _inst_1 _inst_2}, (Function.Injective.{succ u3, succ u2} β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (ContinuousOpenMap.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : β) => γ) _x) (ContinuousMapClass.toFunLike.{max u3 u2, u3, u2} (ContinuousOpenMap.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (ContinuousOpenMapClass.toContinuousMapClass.{max u3 u2, u3, u2} (ContinuousOpenMap.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (ContinuousOpenMap.instContinuousOpenMapClassContinuousOpenMap.{u3, u2} β γ _inst_2 _inst_3))) g)) -> (Iff (Eq.{max (succ u1) (succ u2)} (ContinuousOpenMap.{u1, u2} α γ _inst_1 _inst_3) (ContinuousOpenMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f₁) (ContinuousOpenMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u1) (succ u3)} (ContinuousOpenMap.{u1, u3} α β _inst_1 _inst_2) f₁ f₂))
Case conversion may be inaccurate. Consider using '#align continuous_open_map.cancel_left ContinuousOpenMap.cancel_leftₓ'. -/
theorem cancel_left {g : β →CO γ} {f₁ f₂ : α →CO β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align continuous_open_map.cancel_left ContinuousOpenMap.cancel_left

end ContinuousOpenMap

