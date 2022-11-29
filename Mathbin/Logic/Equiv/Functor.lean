/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Simon Hudon, Scott Morrison
-/
import Mathbin.Control.Bifunctor
import Mathbin.Logic.Equiv.Defs

/-!
# Functor and bifunctors can be applied to `equiv`s.

We define
```lean
def functor.map_equiv (f : Type u → Type v) [functor f] [is_lawful_functor f] :
  α ≃ β → f α ≃ f β
```
and
```lean
def bifunctor.map_equiv (F : Type u → Type v → Type w) [bifunctor F] [is_lawful_bifunctor F] :
  α ≃ β → α' ≃ β' → F α α' ≃ F β β'
```
-/


universe u v w

variable {α β : Type u}

open Equiv

namespace Functor

variable (f : Type u → Type v) [Functor f] [IsLawfulFunctor f]

/-- Apply a functor to an `equiv`. -/
def mapEquiv (h : α ≃ β) : f α ≃ f β where
  toFun := map h
  invFun := map h.symm
  left_inv x := by simp [map_map]
  right_inv x := by simp [map_map]
#align functor.map_equiv Functor.mapEquiv

/- warning: functor.map_equiv_apply -> Functor.map_equiv_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{u}} (f : Type.{u} -> Type.{v}) [_inst_1 : Functor.{u, v} f] [_inst_2 : IsLawfulFunctor.{u, v} f _inst_1] (h : Equiv.{succ u, succ u} α β) (x : f α), Eq.{succ v} (f β) (coeFn.{max 1 (succ v), succ v} (Equiv.{succ v, succ v} (f α) (f β)) (fun (_x : Equiv.{succ v, succ v} (f α) (f β)) => (f α) -> (f β)) (Equiv.hasCoeToFun.{succ v, succ v} (f α) (f β)) (Functor.mapEquiv.{u, v} α β f _inst_1 _inst_2 h) x) (Functor.map.{u, v} f _inst_1 α β (coeFn.{max 1 (succ u), succ u} (Equiv.{succ u, succ u} α β) (fun (_x : Equiv.{succ u, succ u} α β) => α -> β) (Equiv.hasCoeToFun.{succ u, succ u} α β) h) x)
but is expected to have type
  forall (f : Type.{u} -> Type.{v}) [inst._@.Mathlib.Data.Equiv.Functor._hyg.140 : Functor.{u, v} f] [inst._@.Mathlib.Data.Equiv.Functor._hyg.143 : LawfulFunctor.{u, v} f inst._@.Mathlib.Data.Equiv.Functor._hyg.140] {α : Type.{u}} {β : Type.{u}} (h : Equiv.{succ u, succ u} α β) (x : f α), Eq.{succ v} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : f α) => f β) x) (FunLike.coe.{succ v, succ v, succ v} (Equiv.{succ v, succ v} (f α) (f β)) (f α) (fun (a : f α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : f α) => f β) a) (EmbeddingLike.toFunLike.{succ v, succ v, succ v} (Equiv.{succ v, succ v} (f α) (f β)) (f α) (f β) (EquivLike.toEmbeddingLike.{succ v, succ v, succ v} (Equiv.{succ v, succ v} (f α) (f β)) (f α) (f β) (Equiv.instEquivLikeEquiv.{succ v, succ v} (f α) (f β)))) (Functor.map_equiv.{u, v} f inst._@.Mathlib.Data.Equiv.Functor._hyg.140 inst._@.Mathlib.Data.Equiv.Functor._hyg.143 α β h) x) (Functor.map.{u, v} f inst._@.Mathlib.Data.Equiv.Functor._hyg.140 α β (FunLike.coe.{succ u, succ u, succ u} (Equiv.{succ u, succ u} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => β) a) (EmbeddingLike.toFunLike.{succ u, succ u, succ u} (Equiv.{succ u, succ u} α β) α β (EquivLike.toEmbeddingLike.{succ u, succ u, succ u} (Equiv.{succ u, succ u} α β) α β (Equiv.instEquivLikeEquiv.{succ u, succ u} α β))) h) x)
Case conversion may be inaccurate. Consider using '#align functor.map_equiv_apply Functor.map_equiv_applyₓ'. -/
@[simp]
theorem map_equiv_apply (h : α ≃ β) (x : f α) : (mapEquiv f h : f α ≃ f β) x = map h x :=
  rfl
#align functor.map_equiv_apply Functor.map_equiv_apply

/- warning: functor.map_equiv_symm_apply -> Functor.map_equiv_symm_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{u}} (f : Type.{u} -> Type.{v}) [_inst_1 : Functor.{u, v} f] [_inst_2 : IsLawfulFunctor.{u, v} f _inst_1] (h : Equiv.{succ u, succ u} α β) (y : f β), Eq.{succ v} (f α) (coeFn.{max 1 (succ v), succ v} (Equiv.{succ v, succ v} (f β) (f α)) (fun (_x : Equiv.{succ v, succ v} (f β) (f α)) => (f β) -> (f α)) (Equiv.hasCoeToFun.{succ v, succ v} (f β) (f α)) (Equiv.symm.{succ v, succ v} (f α) (f β) (Functor.mapEquiv.{u, v} α β f _inst_1 _inst_2 h)) y) (Functor.map.{u, v} f _inst_1 β α (coeFn.{max 1 (succ u), succ u} (Equiv.{succ u, succ u} β α) (fun (_x : Equiv.{succ u, succ u} β α) => β -> α) (Equiv.hasCoeToFun.{succ u, succ u} β α) (Equiv.symm.{succ u, succ u} α β h)) y)
but is expected to have type
  forall (f : Type.{u} -> Type.{v}) [inst._@.Mathlib.Data.Equiv.Functor._hyg.189 : Functor.{u, v} f] [inst._@.Mathlib.Data.Equiv.Functor._hyg.192 : LawfulFunctor.{u, v} f inst._@.Mathlib.Data.Equiv.Functor._hyg.189] {α : Type.{u}} {β : Type.{u}} (h : Equiv.{succ u, succ u} α β) (y : f β), Eq.{succ v} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : f β) => f α) y) (FunLike.coe.{succ v, succ v, succ v} (Equiv.{succ v, succ v} (f β) (f α)) (f β) (fun (a : f β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : f β) => f α) a) (EmbeddingLike.toFunLike.{succ v, succ v, succ v} (Equiv.{succ v, succ v} (f β) (f α)) (f β) (f α) (EquivLike.toEmbeddingLike.{succ v, succ v, succ v} (Equiv.{succ v, succ v} (f β) (f α)) (f β) (f α) (Equiv.instEquivLikeEquiv.{succ v, succ v} (f β) (f α)))) (Equiv.symm.{succ v, succ v} (f α) (f β) (Functor.map_equiv.{u, v} f inst._@.Mathlib.Data.Equiv.Functor._hyg.189 inst._@.Mathlib.Data.Equiv.Functor._hyg.192 α β h)) y) (Functor.map.{u, v} f inst._@.Mathlib.Data.Equiv.Functor._hyg.189 β α (FunLike.coe.{succ u, succ u, succ u} (Equiv.{succ u, succ u} β α) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => α) a) (EmbeddingLike.toFunLike.{succ u, succ u, succ u} (Equiv.{succ u, succ u} β α) β α (EquivLike.toEmbeddingLike.{succ u, succ u, succ u} (Equiv.{succ u, succ u} β α) β α (Equiv.instEquivLikeEquiv.{succ u, succ u} β α))) (Equiv.symm.{succ u, succ u} α β h)) y)
Case conversion may be inaccurate. Consider using '#align functor.map_equiv_symm_apply Functor.map_equiv_symm_applyₓ'. -/
@[simp]
theorem map_equiv_symm_apply (h : α ≃ β) (y : f β) :
    (mapEquiv f h : f α ≃ f β).symm y = map h.symm y :=
  rfl
#align functor.map_equiv_symm_apply Functor.map_equiv_symm_apply

@[simp]
theorem map_equiv_refl : mapEquiv f (Equiv.refl α) = Equiv.refl (f α) := by
  ext x
  simp only [map_equiv_apply, refl_apply]
  exact IsLawfulFunctor.id_map x
#align functor.map_equiv_refl Functor.map_equiv_refl

end Functor

namespace Bifunctor

variable {α' β' : Type v} (F : Type u → Type v → Type w) [Bifunctor F] [IsLawfulBifunctor F]

/-- Apply a bifunctor to a pair of `equiv`s. -/
def mapEquiv (h : α ≃ β) (h' : α' ≃ β') : F α α' ≃ F β β' where
  toFun := bimap h h'
  invFun := bimap h.symm h'.symm
  left_inv x := by simp [bimap_bimap, id_bimap]
  right_inv x := by simp [bimap_bimap, id_bimap]
#align bifunctor.map_equiv Bifunctor.mapEquiv

@[simp]
theorem map_equiv_apply (h : α ≃ β) (h' : α' ≃ β') (x : F α α') :
    (mapEquiv F h h' : F α α' ≃ F β β') x = bimap h h' x :=
  rfl
#align bifunctor.map_equiv_apply Bifunctor.map_equiv_apply

@[simp]
theorem map_equiv_symm_apply (h : α ≃ β) (h' : α' ≃ β') (y : F β β') :
    (mapEquiv F h h' : F α α' ≃ F β β').symm y = bimap h.symm h'.symm y :=
  rfl
#align bifunctor.map_equiv_symm_apply Bifunctor.map_equiv_symm_apply

@[simp]
theorem map_equiv_refl_refl : mapEquiv F (Equiv.refl α) (Equiv.refl α') = Equiv.refl (F α α') := by
  ext x
  simp [id_bimap]
#align bifunctor.map_equiv_refl_refl Bifunctor.map_equiv_refl_refl

end Bifunctor

