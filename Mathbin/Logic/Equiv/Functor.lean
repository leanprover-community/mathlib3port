/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Simon Hudon, Scott Morrison

! This file was ported from Lean 3 source module logic.equiv.functor
! leanprover-community/mathlib commit aba57d4d3dae35460225919dcd82fe91355162f9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
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
  forall {α : Type.{u1}} {β : Type.{u1}} (f : Type.{u1} -> Type.{u2}) [_inst_1 : Functor.{u1, u2} f] [_inst_2 : IsLawfulFunctor.{u1, u2} f _inst_1] (h : Equiv.{succ u1, succ u1} α β) (x : f α), Eq.{succ u2} (f β) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (f α) (f β)) (fun (_x : Equiv.{succ u2, succ u2} (f α) (f β)) => (f α) -> (f β)) (Equiv.hasCoeToFun.{succ u2, succ u2} (f α) (f β)) (Functor.mapEquiv.{u1, u2} α β f _inst_1 _inst_2 h) x) (Functor.map.{u1, u2} f _inst_1 α β (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α β) (fun (_x : Equiv.{succ u1, succ u1} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u1} α β) h) x)
but is expected to have type
  forall (α : Type.{u1} -> Type.{u2}) [β : Functor.{u1, u2} α] [f : LawfulFunctor.{u1, u2} α β] {_inst_1 : Type.{u1}} {_inst_2 : Type.{u1}} (h : Equiv.{succ u1, succ u1} _inst_1 _inst_2) (x : α _inst_1), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α _inst_1) => α _inst_2) x) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (α _inst_1) (α _inst_2)) (α _inst_1) (fun (_x : α _inst_1) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α _inst_1) => α _inst_2) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (α _inst_1) (α _inst_2)) (α _inst_1) (α _inst_2) (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (α _inst_1) (α _inst_2)) (α _inst_1) (α _inst_2) (Equiv.instEquivLikeEquiv.{succ u2, succ u2} (α _inst_1) (α _inst_2)))) (Functor.map_equiv.{u1, u2} α β f _inst_1 _inst_2 h) x) (Functor.map.{u1, u2} α β _inst_1 _inst_2 (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} _inst_1 _inst_2) _inst_1 (fun (_x : _inst_1) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : _inst_1) => _inst_2) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} _inst_1 _inst_2) _inst_1 _inst_2 (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} _inst_1 _inst_2) _inst_1 _inst_2 (Equiv.instEquivLikeEquiv.{succ u1, succ u1} _inst_1 _inst_2))) h) x)
Case conversion may be inaccurate. Consider using '#align functor.map_equiv_apply Functor.map_equiv_applyₓ'. -/
@[simp]
theorem map_equiv_apply (h : α ≃ β) (x : f α) : (mapEquiv f h : f α ≃ f β) x = map h x :=
  rfl
#align functor.map_equiv_apply Functor.map_equiv_apply

/- warning: functor.map_equiv_symm_apply -> Functor.map_equiv_symm_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} (f : Type.{u1} -> Type.{u2}) [_inst_1 : Functor.{u1, u2} f] [_inst_2 : IsLawfulFunctor.{u1, u2} f _inst_1] (h : Equiv.{succ u1, succ u1} α β) (y : f β), Eq.{succ u2} (f α) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (f β) (f α)) (fun (_x : Equiv.{succ u2, succ u2} (f β) (f α)) => (f β) -> (f α)) (Equiv.hasCoeToFun.{succ u2, succ u2} (f β) (f α)) (Equiv.symm.{succ u2, succ u2} (f α) (f β) (Functor.mapEquiv.{u1, u2} α β f _inst_1 _inst_2 h)) y) (Functor.map.{u1, u2} f _inst_1 β α (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} β α) (fun (_x : Equiv.{succ u1, succ u1} β α) => β -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} β α) (Equiv.symm.{succ u1, succ u1} α β h)) y)
but is expected to have type
  forall (α : Type.{u1} -> Type.{u2}) [β : Functor.{u1, u2} α] [f : LawfulFunctor.{u1, u2} α β] {_inst_1 : Type.{u1}} {_inst_2 : Type.{u1}} (h : Equiv.{succ u1, succ u1} _inst_1 _inst_2) (y : α _inst_2), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α _inst_2) => α _inst_1) y) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (α _inst_2) (α _inst_1)) (α _inst_2) (fun (_x : α _inst_2) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α _inst_2) => α _inst_1) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (α _inst_2) (α _inst_1)) (α _inst_2) (α _inst_1) (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (α _inst_2) (α _inst_1)) (α _inst_2) (α _inst_1) (Equiv.instEquivLikeEquiv.{succ u2, succ u2} (α _inst_2) (α _inst_1)))) (Equiv.symm.{succ u2, succ u2} (α _inst_1) (α _inst_2) (Functor.map_equiv.{u1, u2} α β f _inst_1 _inst_2 h)) y) (Functor.map.{u1, u2} α β _inst_2 _inst_1 (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} _inst_2 _inst_1) _inst_2 (fun (_x : _inst_2) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : _inst_2) => _inst_1) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} _inst_2 _inst_1) _inst_2 _inst_1 (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} _inst_2 _inst_1) _inst_2 _inst_1 (Equiv.instEquivLikeEquiv.{succ u1, succ u1} _inst_2 _inst_1))) (Equiv.symm.{succ u1, succ u1} _inst_1 _inst_2 h)) y)
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
def mapEquiv (h : α ≃ β) (h' : α' ≃ β') :
    F α α' ≃ F β β' where 
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

