/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux

! This file was ported from Lean 3 source module topology.continuous_function.cocompact_map
! leanprover-community/mathlib commit 3e32bc908f617039c74c06ea9a897e30c30803c2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.ContinuousFunction.Basic

/-!
# Cocompact continuous maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The type of *cocompact continuous maps* are those which tend to the cocompact filter on the
codomain along the cocompact filter on the domain. When the domain and codomain are Hausdorff, this
is equivalent to many other conditions, including that preimages of compact sets are compact. -/


universe u v w

open Filter Set

/-! ### Cocompact continuous maps -/


#print CocompactMap /-
/-- A *cocompact continuous map* is a continuous function between topological spaces which
tends to the cocompact filter along the cocompact filter. Functions for which preimages of compact
sets are compact always satisfy this property, and the converse holds for cocompact continuous maps
when the codomain is Hausdorff (see `cocompact_map.tendsto_of_forall_preimage` and
`cocompact_map.is_compact_preimage`).

Cocompact maps thus generalise proper maps, with which they correspond when the codomain is
Hausdorff. -/
structure CocompactMap (α : Type u) (β : Type v) [TopologicalSpace α] [TopologicalSpace β] extends
  ContinuousMap α β : Type max u v where
  cocompact_tendsto' : Tendsto to_fun (cocompact α) (cocompact β)
#align cocompact_map CocompactMap
-/

section

#print CocompactMapClass /-
/-- `cocompact_map_class F α β` states that `F` is a type of cocompact continuous maps.

You should also extend this typeclass when you extend `cocompact_map`. -/
class CocompactMapClass (F : Type _) (α β : outParam <| Type _) [TopologicalSpace α]
  [TopologicalSpace β] extends ContinuousMapClass F α β where
  cocompact_tendsto (f : F) : Tendsto f (cocompact α) (cocompact β)
#align cocompact_map_class CocompactMapClass
-/

end

namespace CocompactMapClass

variable {F α β : Type _} [TopologicalSpace α] [TopologicalSpace β] [CocompactMapClass F α β]

instance : CoeTC F (CocompactMap α β) :=
  ⟨fun f => ⟨f, cocompact_tendsto f⟩⟩

end CocompactMapClass

export CocompactMapClass (cocompact_tendsto)

namespace CocompactMap

section Basics

variable {α β γ δ : Type _} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  [TopologicalSpace δ]

instance : CocompactMapClass (CocompactMap α β) α β
    where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr
  map_continuous f := f.continuous_toFun
  cocompact_tendsto f := f.cocompact_tendsto'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (CocompactMap α β) fun _ => α → β :=
  FunLike.hasCoeToFun

/- warning: cocompact_map.coe_to_continuous_fun -> CocompactMap.coe_toContinuousMap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : CocompactMap.{u1, u2} α β _inst_1 _inst_2}, Eq.{max (succ u1) (succ u2)} ((fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CocompactMap.toContinuousMap.{u1, u2} α β _inst_1 _inst_2 f)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (CocompactMap.toContinuousMap.{u1, u2} α β _inst_1 _inst_2 f)) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (CocompactMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CocompactMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CocompactMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : CocompactMap.{u2, u1} α β _inst_1 _inst_2}, Eq.{max (succ u2) (succ u1)} (forall (a : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (CocompactMap.toContinuousMap.{u2, u1} α β _inst_1 _inst_2 f)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (CocompactMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (CocompactMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CocompactMapClass.toContinuousMapClass.{max u2 u1, u2, u1} (CocompactMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CocompactMap.instCocompactMapClassCocompactMap.{u2, u1} α β _inst_1 _inst_2))) f)
Case conversion may be inaccurate. Consider using '#align cocompact_map.coe_to_continuous_fun CocompactMap.coe_toContinuousMapₓ'. -/
@[simp]
theorem coe_toContinuousMap {f : CocompactMap α β} : (f.toContinuousMap : α → β) = f :=
  rfl
#align cocompact_map.coe_to_continuous_fun CocompactMap.coe_toContinuousMap

/- warning: cocompact_map.ext -> CocompactMap.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : CocompactMap.{u1, u2} α β _inst_1 _inst_2} {g : CocompactMap.{u1, u2} α β _inst_1 _inst_2}, (forall (x : α), Eq.{succ u2} β (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (CocompactMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CocompactMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CocompactMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f x) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (CocompactMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CocompactMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CocompactMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g x)) -> (Eq.{succ (max u1 u2)} (CocompactMap.{u1, u2} α β _inst_1 _inst_2) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : CocompactMap.{u2, u1} α β _inst_1 _inst_2} {g : CocompactMap.{u2, u1} α β _inst_1 _inst_2}, (forall (x : α), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (CocompactMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (CocompactMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CocompactMapClass.toContinuousMapClass.{max u2 u1, u2, u1} (CocompactMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CocompactMap.instCocompactMapClassCocompactMap.{u2, u1} α β _inst_1 _inst_2))) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (CocompactMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (CocompactMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CocompactMapClass.toContinuousMapClass.{max u2 u1, u2, u1} (CocompactMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CocompactMap.instCocompactMapClassCocompactMap.{u2, u1} α β _inst_1 _inst_2))) g x)) -> (Eq.{max (succ u2) (succ u1)} (CocompactMap.{u2, u1} α β _inst_1 _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align cocompact_map.ext CocompactMap.extₓ'. -/
@[ext]
theorem ext {f g : CocompactMap α β} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h
#align cocompact_map.ext CocompactMap.ext

/- warning: cocompact_map.copy -> CocompactMap.copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : CocompactMap.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (CocompactMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CocompactMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CocompactMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)) -> (CocompactMap.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : CocompactMap.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (CocompactMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (CocompactMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CocompactMapClass.toContinuousMapClass.{max u1 u2, u1, u2} (CocompactMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CocompactMap.instCocompactMapClassCocompactMap.{u1, u2} α β _inst_1 _inst_2))) f)) -> (CocompactMap.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align cocompact_map.copy CocompactMap.copyₓ'. -/
/-- Copy of a `cocompact_map` with a new `to_fun` equal to the old one. Useful
to fix definitional equalities. -/
protected def copy (f : CocompactMap α β) (f' : α → β) (h : f' = f) : CocompactMap α β
    where
  toFun := f'
  continuous_toFun := by rw [h]; exact f.continuous_to_fun
  cocompact_tendsto' := by simp_rw [h]; exact f.cocompact_tendsto'
#align cocompact_map.copy CocompactMap.copy

/- warning: cocompact_map.coe_copy -> CocompactMap.coe_copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : CocompactMap.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (CocompactMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CocompactMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CocompactMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (CocompactMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CocompactMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CocompactMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (CocompactMap.copy.{u1, u2} α β _inst_1 _inst_2 f f' h)) f'
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : CocompactMap.{u2, u1} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (CocompactMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (CocompactMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CocompactMapClass.toContinuousMapClass.{max u2 u1, u2, u1} (CocompactMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CocompactMap.instCocompactMapClassCocompactMap.{u2, u1} α β _inst_1 _inst_2))) f)), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (CocompactMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (CocompactMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CocompactMapClass.toContinuousMapClass.{max u2 u1, u2, u1} (CocompactMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CocompactMap.instCocompactMapClassCocompactMap.{u2, u1} α β _inst_1 _inst_2))) (CocompactMap.copy.{u2, u1} α β _inst_1 _inst_2 f f' h)) f'
Case conversion may be inaccurate. Consider using '#align cocompact_map.coe_copy CocompactMap.coe_copyₓ'. -/
@[simp]
theorem coe_copy (f : CocompactMap α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align cocompact_map.coe_copy CocompactMap.coe_copy

/- warning: cocompact_map.copy_eq -> CocompactMap.copy_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : CocompactMap.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (CocompactMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CocompactMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CocompactMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)), Eq.{succ (max u1 u2)} (CocompactMap.{u1, u2} α β _inst_1 _inst_2) (CocompactMap.copy.{u1, u2} α β _inst_1 _inst_2 f f' h) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : CocompactMap.{u2, u1} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (CocompactMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (CocompactMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CocompactMapClass.toContinuousMapClass.{max u2 u1, u2, u1} (CocompactMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CocompactMap.instCocompactMapClassCocompactMap.{u2, u1} α β _inst_1 _inst_2))) f)), Eq.{max (succ u2) (succ u1)} (CocompactMap.{u2, u1} α β _inst_1 _inst_2) (CocompactMap.copy.{u2, u1} α β _inst_1 _inst_2 f f' h) f
Case conversion may be inaccurate. Consider using '#align cocompact_map.copy_eq CocompactMap.copy_eqₓ'. -/
theorem copy_eq (f : CocompactMap α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align cocompact_map.copy_eq CocompactMap.copy_eq

/- warning: cocompact_map.coe_mk -> CocompactMap.coe_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (h : Filter.Tendsto.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f) (Filter.cocompact.{u1} α _inst_1) (Filter.cocompact.{u2} β _inst_2)), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (CocompactMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CocompactMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CocompactMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (CocompactMap.mk.{u1, u2} α β _inst_1 _inst_2 f h)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : ContinuousMap.{u2, u1} α β _inst_1 _inst_2) (h : Filter.Tendsto.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) f) (Filter.cocompact.{u2} α _inst_1) (Filter.cocompact.{u1} β _inst_2)), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (CocompactMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (CocompactMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CocompactMapClass.toContinuousMapClass.{max u2 u1, u2, u1} (CocompactMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CocompactMap.instCocompactMapClassCocompactMap.{u2, u1} α β _inst_1 _inst_2))) (CocompactMap.mk.{u2, u1} α β _inst_1 _inst_2 f h)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) f)
Case conversion may be inaccurate. Consider using '#align cocompact_map.coe_mk CocompactMap.coe_mkₓ'. -/
@[simp]
theorem coe_mk (f : C(α, β)) (h : Tendsto f (cocompact α) (cocompact β)) :
    ⇑(⟨f, h⟩ : CocompactMap α β) = f :=
  rfl
#align cocompact_map.coe_mk CocompactMap.coe_mk

section

variable (α)

#print CocompactMap.id /-
/-- The identity as a cocompact continuous map. -/
protected def id : CocompactMap α α :=
  ⟨ContinuousMap.id _, tendsto_id⟩
#align cocompact_map.id CocompactMap.id
-/

/- warning: cocompact_map.coe_id -> CocompactMap.coe_id is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} α], Eq.{succ u1} (α -> α) (coeFn.{succ u1, succ u1} (CocompactMap.{u1, u1} α α _inst_1 _inst_1) (fun (_x : CocompactMap.{u1, u1} α α _inst_1 _inst_1) => α -> α) (CocompactMap.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (CocompactMap.id.{u1} α _inst_1)) (id.{succ u1} α)
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} α], Eq.{succ u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => α) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (CocompactMap.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => α) _x) (ContinuousMapClass.toFunLike.{u1, u1, u1} (CocompactMap.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (CocompactMapClass.toContinuousMapClass.{u1, u1, u1} (CocompactMap.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (CocompactMap.instCocompactMapClassCocompactMap.{u1, u1} α α _inst_1 _inst_1))) (CocompactMap.id.{u1} α _inst_1)) (id.{succ u1} α)
Case conversion may be inaccurate. Consider using '#align cocompact_map.coe_id CocompactMap.coe_idₓ'. -/
@[simp]
theorem coe_id : ⇑(CocompactMap.id α) = id :=
  rfl
#align cocompact_map.coe_id CocompactMap.coe_id

end

instance : Inhabited (CocompactMap α α) :=
  ⟨CocompactMap.id α⟩

#print CocompactMap.comp /-
/-- The composition of cocompact continuous maps, as a cocompact continuous map. -/
def comp (f : CocompactMap β γ) (g : CocompactMap α β) : CocompactMap α γ :=
  ⟨f.toContinuousMap.comp g, (cocompact_tendsto f).comp (cocompact_tendsto g)⟩
#align cocompact_map.comp CocompactMap.comp
-/

/- warning: cocompact_map.coe_comp -> CocompactMap.coe_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (f : CocompactMap.{u2, u3} β γ _inst_2 _inst_3) (g : CocompactMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (α -> γ) (coeFn.{succ (max u1 u3), max (succ u1) (succ u3)} (CocompactMap.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : CocompactMap.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (CocompactMap.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (CocompactMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g)) (Function.comp.{succ u1, succ u2, succ u3} α β γ (coeFn.{succ (max u2 u3), max (succ u2) (succ u3)} (CocompactMap.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : CocompactMap.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (CocompactMap.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (CocompactMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CocompactMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CocompactMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] (f : CocompactMap.{u3, u2} β γ _inst_2 _inst_3) (g : CocompactMap.{u1, u3} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => γ) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (CocompactMap.{u1, u2} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => γ) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (CocompactMap.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (CocompactMapClass.toContinuousMapClass.{max u1 u2, u1, u2} (CocompactMap.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (CocompactMap.instCocompactMapClassCocompactMap.{u1, u2} α γ _inst_1 _inst_3))) (CocompactMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g)) (Function.comp.{succ u1, succ u3, succ u2} α β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (CocompactMap.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : β) => γ) _x) (ContinuousMapClass.toFunLike.{max u3 u2, u3, u2} (CocompactMap.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (CocompactMapClass.toContinuousMapClass.{max u3 u2, u3, u2} (CocompactMap.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (CocompactMap.instCocompactMapClassCocompactMap.{u3, u2} β γ _inst_2 _inst_3))) f) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (CocompactMap.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u3, u1, u3} (CocompactMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CocompactMapClass.toContinuousMapClass.{max u1 u3, u1, u3} (CocompactMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CocompactMap.instCocompactMapClassCocompactMap.{u1, u3} α β _inst_1 _inst_2))) g))
Case conversion may be inaccurate. Consider using '#align cocompact_map.coe_comp CocompactMap.coe_compₓ'. -/
@[simp]
theorem coe_comp (f : CocompactMap β γ) (g : CocompactMap α β) : ⇑(comp f g) = f ∘ g :=
  rfl
#align cocompact_map.coe_comp CocompactMap.coe_comp

/- warning: cocompact_map.comp_apply -> CocompactMap.comp_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (f : CocompactMap.{u2, u3} β γ _inst_2 _inst_3) (g : CocompactMap.{u1, u2} α β _inst_1 _inst_2) (a : α), Eq.{succ u3} γ (coeFn.{succ (max u1 u3), max (succ u1) (succ u3)} (CocompactMap.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : CocompactMap.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (CocompactMap.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (CocompactMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g) a) (coeFn.{succ (max u2 u3), max (succ u2) (succ u3)} (CocompactMap.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : CocompactMap.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (CocompactMap.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (CocompactMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CocompactMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CocompactMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] (f : CocompactMap.{u3, u2} β γ _inst_2 _inst_3) (g : CocompactMap.{u1, u3} α β _inst_1 _inst_2) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => γ) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (CocompactMap.{u1, u2} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => γ) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (CocompactMap.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (CocompactMapClass.toContinuousMapClass.{max u1 u2, u1, u2} (CocompactMap.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (CocompactMap.instCocompactMapClassCocompactMap.{u1, u2} α γ _inst_1 _inst_3))) (CocompactMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g) a) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (CocompactMap.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : β) => γ) _x) (ContinuousMapClass.toFunLike.{max u3 u2, u3, u2} (CocompactMap.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (CocompactMapClass.toContinuousMapClass.{max u3 u2, u3, u2} (CocompactMap.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (CocompactMap.instCocompactMapClassCocompactMap.{u3, u2} β γ _inst_2 _inst_3))) f (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (CocompactMap.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u3, u1, u3} (CocompactMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CocompactMapClass.toContinuousMapClass.{max u1 u3, u1, u3} (CocompactMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CocompactMap.instCocompactMapClassCocompactMap.{u1, u3} α β _inst_1 _inst_2))) g a))
Case conversion may be inaccurate. Consider using '#align cocompact_map.comp_apply CocompactMap.comp_applyₓ'. -/
@[simp]
theorem comp_apply (f : CocompactMap β γ) (g : CocompactMap α β) (a : α) : comp f g a = f (g a) :=
  rfl
#align cocompact_map.comp_apply CocompactMap.comp_apply

/- warning: cocompact_map.comp_assoc -> CocompactMap.comp_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] (f : CocompactMap.{u3, u4} γ δ _inst_3 _inst_4) (g : CocompactMap.{u2, u3} β γ _inst_2 _inst_3) (h : CocompactMap.{u1, u2} α β _inst_1 _inst_2), Eq.{succ (max u1 u4)} (CocompactMap.{u1, u4} α δ _inst_1 _inst_4) (CocompactMap.comp.{u1, u2, u4} α β δ _inst_1 _inst_2 _inst_4 (CocompactMap.comp.{u2, u3, u4} β γ δ _inst_2 _inst_3 _inst_4 f g) h) (CocompactMap.comp.{u1, u3, u4} α γ δ _inst_1 _inst_3 _inst_4 f (CocompactMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g h))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u4}} {δ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u4} γ] [_inst_4 : TopologicalSpace.{u3} δ] (f : CocompactMap.{u4, u3} γ δ _inst_3 _inst_4) (g : CocompactMap.{u2, u4} β γ _inst_2 _inst_3) (h : CocompactMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (CocompactMap.{u1, u3} α δ _inst_1 _inst_4) (CocompactMap.comp.{u1, u2, u3} α β δ _inst_1 _inst_2 _inst_4 (CocompactMap.comp.{u2, u4, u3} β γ δ _inst_2 _inst_3 _inst_4 f g) h) (CocompactMap.comp.{u1, u4, u3} α γ δ _inst_1 _inst_3 _inst_4 f (CocompactMap.comp.{u1, u2, u4} α β γ _inst_1 _inst_2 _inst_3 g h))
Case conversion may be inaccurate. Consider using '#align cocompact_map.comp_assoc CocompactMap.comp_assocₓ'. -/
@[simp]
theorem comp_assoc (f : CocompactMap γ δ) (g : CocompactMap β γ) (h : CocompactMap α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align cocompact_map.comp_assoc CocompactMap.comp_assoc

/- warning: cocompact_map.id_comp -> CocompactMap.id_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : CocompactMap.{u1, u2} α β _inst_1 _inst_2), Eq.{succ (max u1 u2)} (CocompactMap.{u1, u2} α β _inst_1 _inst_2) (CocompactMap.comp.{u1, u2, u2} α β β _inst_1 _inst_2 _inst_2 (CocompactMap.id.{u2} β _inst_2) f) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : CocompactMap.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (CocompactMap.{u2, u1} α β _inst_1 _inst_2) (CocompactMap.comp.{u2, u1, u1} α β β _inst_1 _inst_2 _inst_2 (CocompactMap.id.{u1} β _inst_2) f) f
Case conversion may be inaccurate. Consider using '#align cocompact_map.id_comp CocompactMap.id_compₓ'. -/
@[simp]
theorem id_comp (f : CocompactMap α β) : (CocompactMap.id _).comp f = f :=
  ext fun _ => rfl
#align cocompact_map.id_comp CocompactMap.id_comp

/- warning: cocompact_map.comp_id -> CocompactMap.comp_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : CocompactMap.{u1, u2} α β _inst_1 _inst_2), Eq.{succ (max u1 u2)} (CocompactMap.{u1, u2} α β _inst_1 _inst_2) (CocompactMap.comp.{u1, u1, u2} α α β _inst_1 _inst_1 _inst_2 f (CocompactMap.id.{u1} α _inst_1)) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : CocompactMap.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (CocompactMap.{u2, u1} α β _inst_1 _inst_2) (CocompactMap.comp.{u2, u2, u1} α α β _inst_1 _inst_1 _inst_2 f (CocompactMap.id.{u2} α _inst_1)) f
Case conversion may be inaccurate. Consider using '#align cocompact_map.comp_id CocompactMap.comp_idₓ'. -/
@[simp]
theorem comp_id (f : CocompactMap α β) : f.comp (CocompactMap.id _) = f :=
  ext fun _ => rfl
#align cocompact_map.comp_id CocompactMap.comp_id

#print CocompactMap.tendsto_of_forall_preimage /-
theorem tendsto_of_forall_preimage {f : α → β} (h : ∀ s, IsCompact s → IsCompact (f ⁻¹' s)) :
    Tendsto f (cocompact α) (cocompact β) := fun s hs =>
  match mem_cocompact.mp hs with
  | ⟨t, ht, hts⟩ =>
    mem_map.mpr (mem_cocompact.mpr ⟨f ⁻¹' t, h t ht, by simpa using preimage_mono hts⟩)
#align cocompact_map.tendsto_of_forall_preimage CocompactMap.tendsto_of_forall_preimage
-/

/- warning: cocompact_map.is_compact_preimage -> CocompactMap.isCompact_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_5 : T2Space.{u2} β _inst_2] (f : CocompactMap.{u1, u2} α β _inst_1 _inst_2) {{s : Set.{u2} β}}, (IsCompact.{u2} β _inst_2 s) -> (IsCompact.{u1} α _inst_1 (Set.preimage.{u1, u2} α β (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (CocompactMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CocompactMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CocompactMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f) s))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_5 : T2Space.{u2} β _inst_2] (f : CocompactMap.{u1, u2} α β _inst_1 _inst_2) {{s : Set.{u2} β}}, (IsCompact.{u2} β _inst_2 s) -> (IsCompact.{u1} α _inst_1 (Set.preimage.{u1, u2} α β (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (CocompactMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (CocompactMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CocompactMapClass.toContinuousMapClass.{max u1 u2, u1, u2} (CocompactMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CocompactMap.instCocompactMapClassCocompactMap.{u1, u2} α β _inst_1 _inst_2))) f) s))
Case conversion may be inaccurate. Consider using '#align cocompact_map.is_compact_preimage CocompactMap.isCompact_preimageₓ'. -/
/-- If the codomain is Hausdorff, preimages of compact sets are compact under a cocompact
continuous map. -/
theorem isCompact_preimage [T2Space β] (f : CocompactMap α β) ⦃s : Set β⦄ (hs : IsCompact s) :
    IsCompact (f ⁻¹' s) :=
  by
  obtain ⟨t, ht, hts⟩ :=
    mem_cocompact'.mp
      (by
        simpa only [preimage_image_preimage, preimage_compl] using
          mem_map.mp
            (cocompact_tendsto f <|
              mem_cocompact.mpr ⟨s, hs, compl_subset_compl.mpr (image_preimage_subset f _)⟩))
  exact
    isCompact_of_isClosed_subset ht (hs.is_closed.preimage <| map_continuous f) (by simpa using hts)
#align cocompact_map.is_compact_preimage CocompactMap.isCompact_preimage

end Basics

end CocompactMap

#print Homeomorph.toCocompactMap /-
/-- A homemomorphism is a cocompact map. -/
@[simps]
def Homeomorph.toCocompactMap {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]
    (f : α ≃ₜ β) : CocompactMap α β where
  toFun := f
  continuous_toFun := f.Continuous
  cocompact_tendsto' :=
    by
    refine' CocompactMap.tendsto_of_forall_preimage fun K hK => _
    erw [K.preimage_equiv_eq_image_symm]
    exact hK.image f.symm.continuous
#align homeomorph.to_cocompact_map Homeomorph.toCocompactMap
-/

