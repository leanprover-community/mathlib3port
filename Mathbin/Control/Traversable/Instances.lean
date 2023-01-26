/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module control.traversable.instances
! leanprover-community/mathlib commit f93c11933efbc3c2f0299e47b8ff83e9b539cbf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Control.Applicative
import Mathbin.Data.List.Forall2
import Mathbin.Data.Set.Functor

/-!
# Traversable instances

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides instances of `traversable` for types from the core library: `option`, `list` and
`sum`.
-/


universe u v

section Option

open Functor

variable {F G : Type u → Type u}

variable [Applicative F] [Applicative G]

variable [LawfulApplicative F] [LawfulApplicative G]

/- warning: option.id_traverse -> Option.id_traverse is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (x : Option.{u1} α), Eq.{succ u1} (id.{succ (succ u1)} Type.{u1} (Option.{u1} α)) (Option.traverse.{u1, u1, u1} (id.{succ (succ u1)} Type.{u1}) (Monad.toApplicative.{u1, u1} (id.{succ (succ u1)} Type.{u1}) id.monad.{u1}) α α (id.mk.{succ u1} α) x) x
but is expected to have type
  forall {α : Type.{u1}} (x : Option.{u1} α), Eq.{succ u1} (Id.{u1} (Option.{u1} α)) (Option.traverse.{u1, u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1}) α α (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) α) x) x
Case conversion may be inaccurate. Consider using '#align option.id_traverse Option.id_traverseₓ'. -/
theorem Option.id_traverse {α} (x : Option α) : Option.traverse id.mk x = x := by cases x <;> rfl
#align option.id_traverse Option.id_traverse

/- warning: option.comp_traverse -> Option.comp_traverse is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u1}} {G : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} F] [_inst_2 : Applicative.{u1, u1} G] [_inst_3 : LawfulApplicative.{u1, u1} F _inst_1] [_inst_4 : LawfulApplicative.{u1, u1} G _inst_2] {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u1}} (f : β -> (F γ)) (g : α -> (G β)) (x : Option.{u2} α), Eq.{succ u1} (Functor.Comp.{u1, u1, u1} (fun {β : Type.{u1}} => G β) F (Option.{u1} γ)) (Option.traverse.{u1, u1, u2} (Functor.Comp.{u1, u1, u1} (fun {β : Type.{u1}} => G β) F) (Functor.Comp.applicative.{u1, u1, u1} (fun {β : Type.{u1}} => G β) F _inst_2 _inst_1) α γ (Function.comp.{succ u2, succ u1, succ u1} α (G (F γ)) (Functor.Comp.{u1, u1, u1} (fun {β : Type.{u1}} => G β) F γ) (Functor.Comp.mk.{u1, u1, u1} (fun {β : Type.{u1}} => G β) F γ) (Function.comp.{succ u2, succ u1, succ u1} α (G β) (G (F γ)) (Functor.map.{u1, u1} (fun {β : Type.{u1}} => G β) (Applicative.toFunctor.{u1, u1} (fun {β : Type.{u1}} => G β) _inst_2) β (F γ) f) g)) x) (Functor.Comp.mk.{u1, u1, u1} (fun {β : Type.{u1}} => G β) F (Option.{u1} γ) (Functor.map.{u1, u1} G (Applicative.toFunctor.{u1, u1} G _inst_2) (Option.{u1} β) (F (Option.{u1} γ)) (Option.traverse.{u1, u1, u1} F _inst_1 β γ f) (Option.traverse.{u1, u1, u2} G _inst_2 α β g x)))
but is expected to have type
  forall {F : Type.{u2} -> Type.{u2}} {G : Type.{u2} -> Type.{u2}} [_inst_1 : Applicative.{u2, u2} F] [_inst_2 : Applicative.{u2, u2} G] [_inst_3 : LawfulApplicative.{u2, u2} G _inst_2] {_inst_4 : Type.{u1}} {α : Type.{u2}} {β : Type.{u2}} (γ : α -> (F β)) (f : _inst_4 -> (G α)) (g : Option.{u1} _inst_4), Eq.{succ u2} (Functor.Comp.{u2, u2, u2} G F (Option.{u2} β)) (Option.traverse.{u2, u2, u1} (Functor.Comp.{u2, u2, u2} G F) (Functor.Comp.instApplicativeComp.{u2, u2, u2} G F _inst_2 _inst_1) _inst_4 β (Function.comp.{succ u1, succ u2, succ u2} _inst_4 (G (F β)) (Functor.Comp.{u2, u2, u2} G F β) (Functor.Comp.mk.{u2, u2, u2} G F β) (Function.comp.{succ u1, succ u2, succ u2} _inst_4 (G α) (G (F β)) ((fun (x._@.Mathlib.Control.Traversable.Instances._hyg.175 : α -> (F β)) (x._@.Mathlib.Control.Traversable.Instances._hyg.177 : G α) => Functor.map.{u2, u2} G (Applicative.toFunctor.{u2, u2} G _inst_2) α (F β) x._@.Mathlib.Control.Traversable.Instances._hyg.175 x._@.Mathlib.Control.Traversable.Instances._hyg.177) γ) f)) g) (Functor.Comp.mk.{u2, u2, u2} G F (Option.{u2} β) (Functor.map.{u2, u2} G (Applicative.toFunctor.{u2, u2} G _inst_2) (Option.{u2} α) (F (Option.{u2} β)) (Option.traverse.{u2, u2, u2} F _inst_1 α β γ) (Option.traverse.{u2, u2, u1} G _inst_2 _inst_4 α f g)))
Case conversion may be inaccurate. Consider using '#align option.comp_traverse Option.comp_traverseₓ'. -/
@[nolint unused_arguments]
theorem Option.comp_traverse {α β γ} (f : β → F γ) (g : α → G β) (x : Option α) :
    Option.traverse (comp.mk ∘ (· <$> ·) f ∘ g) x =
      Comp.mk (Option.traverse f <$> Option.traverse g x) :=
  by cases x <;> simp! [functor_norm] <;> rfl
#align option.comp_traverse Option.comp_traverse

/- warning: option.traverse_eq_map_id -> Option.traverse_eq_map_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> β) (x : Option.{u1} α), Eq.{succ u1} (id.{succ (succ u1)} Type.{u1} (Option.{u1} β)) (Traversable.traverse.{u1} (fun {α : Type.{u1}} => Option.{u1} α) Option.traversable.{u1} (id.{succ (succ u1)} Type.{u1}) (Monad.toApplicative.{u1, u1} (id.{succ (succ u1)} Type.{u1}) id.monad.{u1}) α β (Function.comp.{succ u1, succ u1, succ u1} α β (id.{succ (succ u1)} Type.{u1} β) (id.mk.{succ u1} β) f) x) (id.mk.{succ u1} (Option.{u1} β) (Functor.map.{u1, u1} Option.{u1} (Traversable.toFunctor.{u1} Option.{u1} Option.traversable.{u1}) α β f x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> β) (x : Option.{u1} α), Eq.{succ u1} (Id.{u1} (Option.{u1} β)) (Option.traverse.{u1, u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1}) α β (Function.comp.{succ u1, succ u1, succ u1} α β (Id.{u1} β) (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) β) f) x) (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) (Option.{u1} β) (Functor.map.{u1, u1} Option.{u1} instFunctorOption.{u1} α β f x))
Case conversion may be inaccurate. Consider using '#align option.traverse_eq_map_id Option.traverse_eq_map_idₓ'. -/
theorem Option.traverse_eq_map_id {α β} (f : α → β) (x : Option α) :
    traverse (id.mk ∘ f) x = id.mk (f <$> x) := by cases x <;> rfl
#align option.traverse_eq_map_id Option.traverse_eq_map_id

variable (η : ApplicativeTransformation F G)

/- warning: option.naturality -> Option.naturality is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u1}} {G : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} F] [_inst_2 : Applicative.{u1, u1} G] [_inst_3 : LawfulApplicative.{u1, u1} F _inst_1] [_inst_4 : LawfulApplicative.{u1, u1} G _inst_2] (η : ApplicativeTransformation.{u1, u1, u1} F _inst_1 _inst_3 G _inst_2 _inst_4) {α : Type.{u2}} {β : Type.{u1}} (f : α -> (F β)) (x : Option.{u2} α), Eq.{succ u1} (G (Option.{u1} β)) (coeFn.{succ (succ u1), succ (succ u1)} (ApplicativeTransformation.{u1, u1, u1} F _inst_1 _inst_3 G _inst_2 _inst_4) (fun (_x : ApplicativeTransformation.{u1, u1, u1} F _inst_1 _inst_3 G _inst_2 _inst_4) => forall {α : Type.{u1}}, (F α) -> (G α)) (ApplicativeTransformation.hasCoeToFun.{u1, u1, u1} F _inst_1 _inst_3 G _inst_2 _inst_4) η (Option.{u1} β) (Option.traverse.{u1, u1, u2} F _inst_1 α β f x)) (Option.traverse.{u1, u1, u2} G _inst_2 α β (Function.comp.{succ u2, succ u1, succ u1} α (F β) (G β) (coeFn.{succ (succ u1), succ (succ u1)} (ApplicativeTransformation.{u1, u1, u1} F _inst_1 _inst_3 G _inst_2 _inst_4) (fun (_x : ApplicativeTransformation.{u1, u1, u1} F _inst_1 _inst_3 G _inst_2 _inst_4) => forall {α : Type.{u1}}, (F α) -> (G α)) (ApplicativeTransformation.hasCoeToFun.{u1, u1, u1} F _inst_1 _inst_3 G _inst_2 _inst_4) η β) f) x)
but is expected to have type
  forall {F : Type.{u2} -> Type.{u2}} {G : Type.{u2} -> Type.{u2}} [_inst_1 : Applicative.{u2, u2} F] [_inst_2 : Applicative.{u2, u2} G] [_inst_3 : LawfulApplicative.{u2, u2} F _inst_1] [_inst_4 : LawfulApplicative.{u2, u2} G _inst_2] (η : ApplicativeTransformation.{u2, u2, u2} F _inst_1 G _inst_2) {α : Type.{u1}} {β : Type.{u2}} (f : α -> (F β)) (x : Option.{u1} α), Eq.{succ u2} (G (Option.{u2} β)) ((fun {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u2}} => ApplicativeTransformation.app.{u2, u2, u2} F _inst_1 G _inst_2 η α._@.Mathlib.Control.Traversable.Basic._hyg.245) (Option.{u2} β) (Option.traverse.{u2, u2, u1} F _inst_1 α β f x)) (Option.traverse.{u2, u2, u1} G _inst_2 α β (Function.comp.{succ u1, succ u2, succ u2} α (F β) (G β) ((fun {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u2}} => ApplicativeTransformation.app.{u2, u2, u2} F _inst_1 G _inst_2 η α._@.Mathlib.Control.Traversable.Basic._hyg.245) β) f) x)
Case conversion may be inaccurate. Consider using '#align option.naturality Option.naturalityₓ'. -/
theorem Option.naturality {α β} (f : α → F β) (x : Option α) :
    η (Option.traverse f x) = Option.traverse (@η _ ∘ f) x := by
  cases' x with x <;> simp! [*, functor_norm]
#align option.naturality Option.naturality

end Option

instance : IsLawfulTraversable Option :=
  { Option.lawfulMonad with
    id_traverse := @Option.id_traverse
    comp_traverse := @Option.comp_traverse
    traverse_eq_map_id := @Option.traverse_eq_map_id
    naturality := @Option.naturality }

namespace List

variable {F G : Type u → Type u}

variable [Applicative F] [Applicative G]

section

variable [LawfulApplicative F] [LawfulApplicative G]

open Applicative Functor List

/- warning: list.id_traverse -> List.id_traverse is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (xs : List.{u1} α), Eq.{succ u1} (id.{succ (succ u1)} Type.{u1} (List.{u1} α)) (List.traverse.{u1, u1, u1} (id.{succ (succ u1)} Type.{u1}) (Monad.toApplicative.{u1, u1} (id.{succ (succ u1)} Type.{u1}) id.monad.{u1}) α α (id.mk.{succ u1} α) xs) xs
but is expected to have type
  forall {α : Type.{u1}} (xs : List.{u1} α), Eq.{succ u1} (Id.{u1} (List.{u1} α)) (List.traverse.{u1, u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1}) α α (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) α) xs) xs
Case conversion may be inaccurate. Consider using '#align list.id_traverse List.id_traverseₓ'. -/
protected theorem id_traverse {α} (xs : List α) : List.traverse id.mk xs = xs := by
  induction xs <;> simp! [*, functor_norm] <;> rfl
#align list.id_traverse List.id_traverse

/- warning: list.comp_traverse -> List.comp_traverse is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u1}} {G : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} F] [_inst_2 : Applicative.{u1, u1} G] [_inst_3 : LawfulApplicative.{u1, u1} F _inst_1] [_inst_4 : LawfulApplicative.{u1, u1} G _inst_2] {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u1}} (f : β -> (F γ)) (g : α -> (G β)) (x : List.{u2} α), Eq.{succ u1} (Functor.Comp.{u1, u1, u1} (fun {β : Type.{u1}} => G β) F (List.{u1} γ)) (List.traverse.{u1, u1, u2} (Functor.Comp.{u1, u1, u1} (fun {β : Type.{u1}} => G β) F) (Functor.Comp.applicative.{u1, u1, u1} (fun {β : Type.{u1}} => G β) F _inst_2 _inst_1) α γ (Function.comp.{succ u2, succ u1, succ u1} α (G (F γ)) (Functor.Comp.{u1, u1, u1} (fun {β : Type.{u1}} => G β) F γ) (Functor.Comp.mk.{u1, u1, u1} (fun {β : Type.{u1}} => G β) F γ) (Function.comp.{succ u2, succ u1, succ u1} α (G β) (G (F γ)) (Functor.map.{u1, u1} (fun {β : Type.{u1}} => G β) (Applicative.toFunctor.{u1, u1} (fun {β : Type.{u1}} => G β) _inst_2) β (F γ) f) g)) x) (Functor.Comp.mk.{u1, u1, u1} (fun {β : Type.{u1}} => G β) F (List.{u1} γ) (Functor.map.{u1, u1} G (Applicative.toFunctor.{u1, u1} G _inst_2) (List.{u1} β) (F (List.{u1} γ)) (List.traverse.{u1, u1, u1} F _inst_1 β γ f) (List.traverse.{u1, u1, u2} G _inst_2 α β g x)))
but is expected to have type
  forall {F : Type.{u2} -> Type.{u2}} {G : Type.{u2} -> Type.{u2}} [_inst_1 : Applicative.{u2, u2} F] [_inst_2 : Applicative.{u2, u2} G] [_inst_3 : LawfulApplicative.{u2, u2} G _inst_2] {_inst_4 : Type.{u1}} {α : Type.{u2}} {β : Type.{u2}} (γ : α -> (F β)) (f : _inst_4 -> (G α)) (g : List.{u1} _inst_4), Eq.{succ u2} (Functor.Comp.{u2, u2, u2} G F (List.{u2} β)) (List.traverse.{u2, u2, u1} (Functor.Comp.{u2, u2, u2} G F) (Functor.Comp.instApplicativeComp.{u2, u2, u2} G F _inst_2 _inst_1) _inst_4 β (Function.comp.{succ u1, succ u2, succ u2} _inst_4 (G (F β)) (Functor.Comp.{u2, u2, u2} G F β) (Functor.Comp.mk.{u2, u2, u2} G F β) (Function.comp.{succ u1, succ u2, succ u2} _inst_4 (G α) (G (F β)) ((fun (x._@.Mathlib.Control.Traversable.Instances._hyg.980 : α -> (F β)) (x._@.Mathlib.Control.Traversable.Instances._hyg.982 : G α) => Functor.map.{u2, u2} G (Applicative.toFunctor.{u2, u2} G _inst_2) α (F β) x._@.Mathlib.Control.Traversable.Instances._hyg.980 x._@.Mathlib.Control.Traversable.Instances._hyg.982) γ) f)) g) (Functor.Comp.mk.{u2, u2, u2} G F (List.{u2} β) (Functor.map.{u2, u2} G (Applicative.toFunctor.{u2, u2} G _inst_2) (List.{u2} α) (F (List.{u2} β)) (List.traverse.{u2, u2, u2} F _inst_1 α β γ) (List.traverse.{u2, u2, u1} G _inst_2 _inst_4 α f g)))
Case conversion may be inaccurate. Consider using '#align list.comp_traverse List.comp_traverseₓ'. -/
@[nolint unused_arguments]
protected theorem comp_traverse {α β γ} (f : β → F γ) (g : α → G β) (x : List α) :
    List.traverse (comp.mk ∘ (· <$> ·) f ∘ g) x = Comp.mk (List.traverse f <$> List.traverse g x) :=
  by induction x <;> simp! [*, functor_norm] <;> rfl
#align list.comp_traverse List.comp_traverse

/- warning: list.traverse_eq_map_id -> List.traverse_eq_map_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> β) (x : List.{u1} α), Eq.{succ u1} (id.{succ (succ u1)} Type.{u1} (List.{u1} β)) (List.traverse.{u1, u1, u1} (id.{succ (succ u1)} Type.{u1}) (Monad.toApplicative.{u1, u1} (id.{succ (succ u1)} Type.{u1}) id.monad.{u1}) α β (Function.comp.{succ u1, succ u1, succ u1} α β (id.{succ (succ u1)} Type.{u1} β) (id.mk.{succ u1} β) f) x) (id.mk.{succ u1} (List.{u1} β) (Functor.map.{u1, u1} List.{u1} (Traversable.toFunctor.{u1} List.{u1} List.traversable.{u1}) α β f x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> β) (x : List.{u1} α), Eq.{succ u1} (Id.{u1} (List.{u1} β)) (List.traverse.{u1, u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1}) α β (Function.comp.{succ u1, succ u1, succ u1} α β (Id.{u1} β) (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) β) f) x) (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) (List.{u1} β) (Functor.map.{u1, u1} List.{u1} List.instFunctorList.{u1} α β f x))
Case conversion may be inaccurate. Consider using '#align list.traverse_eq_map_id List.traverse_eq_map_idₓ'. -/
protected theorem traverse_eq_map_id {α β} (f : α → β) (x : List α) :
    List.traverse (id.mk ∘ f) x = id.mk (f <$> x) := by
  induction x <;> simp! [*, functor_norm] <;> rfl
#align list.traverse_eq_map_id List.traverse_eq_map_id

variable (η : ApplicativeTransformation F G)

/- warning: list.naturality -> List.naturality is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u1}} {G : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} F] [_inst_2 : Applicative.{u1, u1} G] [_inst_3 : LawfulApplicative.{u1, u1} F _inst_1] [_inst_4 : LawfulApplicative.{u1, u1} G _inst_2] (η : ApplicativeTransformation.{u1, u1, u1} F _inst_1 _inst_3 G _inst_2 _inst_4) {α : Type.{u2}} {β : Type.{u1}} (f : α -> (F β)) (x : List.{u2} α), Eq.{succ u1} (G (List.{u1} β)) (coeFn.{succ (succ u1), succ (succ u1)} (ApplicativeTransformation.{u1, u1, u1} F _inst_1 _inst_3 G _inst_2 _inst_4) (fun (_x : ApplicativeTransformation.{u1, u1, u1} F _inst_1 _inst_3 G _inst_2 _inst_4) => forall {α : Type.{u1}}, (F α) -> (G α)) (ApplicativeTransformation.hasCoeToFun.{u1, u1, u1} F _inst_1 _inst_3 G _inst_2 _inst_4) η (List.{u1} β) (List.traverse.{u1, u1, u2} F _inst_1 α β f x)) (List.traverse.{u1, u1, u2} G _inst_2 α β (Function.comp.{succ u2, succ u1, succ u1} α (F β) (G β) (coeFn.{succ (succ u1), succ (succ u1)} (ApplicativeTransformation.{u1, u1, u1} F _inst_1 _inst_3 G _inst_2 _inst_4) (fun (_x : ApplicativeTransformation.{u1, u1, u1} F _inst_1 _inst_3 G _inst_2 _inst_4) => forall {α : Type.{u1}}, (F α) -> (G α)) (ApplicativeTransformation.hasCoeToFun.{u1, u1, u1} F _inst_1 _inst_3 G _inst_2 _inst_4) η β) f) x)
but is expected to have type
  forall {F : Type.{u2} -> Type.{u2}} {G : Type.{u2} -> Type.{u2}} [_inst_1 : Applicative.{u2, u2} F] [_inst_2 : Applicative.{u2, u2} G] [_inst_3 : LawfulApplicative.{u2, u2} F _inst_1] [_inst_4 : LawfulApplicative.{u2, u2} G _inst_2] (η : ApplicativeTransformation.{u2, u2, u2} F _inst_1 G _inst_2) {α : Type.{u1}} {β : Type.{u2}} (f : α -> (F β)) (x : List.{u1} α), Eq.{succ u2} (G (List.{u2} β)) ((fun {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u2}} => ApplicativeTransformation.app.{u2, u2, u2} F _inst_1 G _inst_2 η α._@.Mathlib.Control.Traversable.Basic._hyg.245) (List.{u2} β) (List.traverse.{u2, u2, u1} F _inst_1 α β f x)) (List.traverse.{u2, u2, u1} G _inst_2 α β (Function.comp.{succ u1, succ u2, succ u2} α (F β) (G β) ((fun {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u2}} => ApplicativeTransformation.app.{u2, u2, u2} F _inst_1 G _inst_2 η α._@.Mathlib.Control.Traversable.Basic._hyg.245) β) f) x)
Case conversion may be inaccurate. Consider using '#align list.naturality List.naturalityₓ'. -/
protected theorem naturality {α β} (f : α → F β) (x : List α) :
    η (List.traverse f x) = List.traverse (@η _ ∘ f) x := by induction x <;> simp! [*, functor_norm]
#align list.naturality List.naturality

open Nat

instance : IsLawfulTraversable.{u} List :=
  { List.lawfulMonad with
    id_traverse := @List.id_traverse
    comp_traverse := @List.comp_traverse
    traverse_eq_map_id := @List.traverse_eq_map_id
    naturality := @List.naturality }

end

section Traverse

variable {α' β' : Type u} (f : α' → F β')

#print List.traverse_nil /-
@[simp]
theorem traverse_nil : traverse f ([] : List α') = (pure [] : F (List β')) :=
  rfl
#align list.traverse_nil List.traverse_nil
-/

/- warning: list.traverse_cons -> List.traverse_cons is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} F] {α' : Type.{u1}} {β' : Type.{u1}} (f : α' -> (F β')) (a : α') (l : List.{u1} α'), Eq.{succ u1} (F (List.{u1} β')) (Traversable.traverse.{u1} List.{u1} List.traversable.{u1} F _inst_1 α' β' f (List.cons.{u1} α' a l)) (Seq.seq.{u1, u1} F (Applicative.toHasSeq.{u1, u1} F _inst_1) (List.{u1} β') (List.{u1} β') (Functor.map.{u1, u1} F (Applicative.toFunctor.{u1, u1} F _inst_1) β' ((List.{u1} β') -> (List.{u1} β')) (fun (_x : β') (_y : List.{u1} β') => List.cons.{u1} β' _x _y) (f a)) (Traversable.traverse.{u1} List.{u1} List.traversable.{u1} F _inst_1 α' β' f l))
but is expected to have type
  forall {F : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} F] {α' : Type.{u1}} {β' : Type.{u1}} (f : α' -> (F β')) (a : α') (l : List.{u1} α'), Eq.{succ u1} (F (List.{u1} β')) (Traversable.traverse.{u1} List.{u1} instTraversableList.{u1} F _inst_1 α' β' f (List.cons.{u1} α' a l)) (Seq.seq.{u1, u1} F (Applicative.toSeq.{u1, u1} F _inst_1) (List.{u1} β') (List.{u1} β') (Functor.map.{u1, u1} F (Applicative.toFunctor.{u1, u1} F _inst_1) β' ((List.{u1} β') -> (List.{u1} β')) (fun (_x : β') (_y : List.{u1} β') => List.cons.{u1} β' _x _y) (f a)) (fun (x._@.Mathlib.Control.Traversable.Instances._hyg.1743 : Unit) => Traversable.traverse.{u1} List.{u1} instTraversableList.{u1} F _inst_1 α' β' f l))
Case conversion may be inaccurate. Consider using '#align list.traverse_cons List.traverse_consₓ'. -/
@[simp]
theorem traverse_cons (a : α') (l : List α') :
    traverse f (a :: l) = (· :: ·) <$> f a <*> traverse f l :=
  rfl
#align list.traverse_cons List.traverse_cons

variable [LawfulApplicative F]

/- warning: list.traverse_append -> List.traverse_append is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} F] {α' : Type.{u1}} {β' : Type.{u1}} (f : α' -> (F β')) [_inst_3 : LawfulApplicative.{u1, u1} F _inst_1] (as : List.{u1} α') (bs : List.{u1} α'), Eq.{succ u1} (F (List.{u1} β')) (Traversable.traverse.{u1} (fun {α' : Type.{u1}} => List.{u1} α') List.traversable.{u1} F _inst_1 α' β' f (Append.append.{u1} (List.{u1} α') (List.hasAppend.{u1} α') as bs)) (Seq.seq.{u1, u1} F (Applicative.toHasSeq.{u1, u1} F _inst_1) (List.{u1} β') (List.{u1} β') (Functor.map.{u1, u1} F (Applicative.toFunctor.{u1, u1} F _inst_1) (List.{u1} β') ((List.{u1} β') -> (List.{u1} β')) (Append.append.{u1} (List.{u1} β') (List.hasAppend.{u1} β')) (Traversable.traverse.{u1} List.{u1} List.traversable.{u1} F _inst_1 α' β' f as)) (Traversable.traverse.{u1} List.{u1} List.traversable.{u1} F _inst_1 α' β' f bs))
but is expected to have type
  forall {F : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} F] {α' : Type.{u1}} {β' : Type.{u1}} (f : α' -> (F β')) [_inst_3 : LawfulApplicative.{u1, u1} F _inst_1] (as : List.{u1} α') (bs : List.{u1} α'), Eq.{succ u1} (F (List.{u1} β')) (Traversable.traverse.{u1} List.{u1} instTraversableList.{u1} F _inst_1 α' β' f (HAppend.hAppend.{u1, u1, u1} (List.{u1} α') (List.{u1} α') (List.{u1} α') (instHAppend.{u1} (List.{u1} α') (List.instAppendList.{u1} α')) as bs)) (Seq.seq.{u1, u1} F (Applicative.toSeq.{u1, u1} F _inst_1) (List.{u1} β') (List.{u1} β') (Functor.map.{u1, u1} F (Applicative.toFunctor.{u1, u1} F _inst_1) (List.{u1} β') ((List.{u1} β') -> (List.{u1} β')) (fun (x._@.Mathlib.Control.Traversable.Instances._hyg.1825 : List.{u1} β') (x._@.Mathlib.Control.Traversable.Instances._hyg.1827 : List.{u1} β') => HAppend.hAppend.{u1, u1, u1} (List.{u1} β') (List.{u1} β') (List.{u1} β') (instHAppend.{u1} (List.{u1} β') (List.instAppendList.{u1} β')) x._@.Mathlib.Control.Traversable.Instances._hyg.1825 x._@.Mathlib.Control.Traversable.Instances._hyg.1827) (Traversable.traverse.{u1} List.{u1} instTraversableList.{u1} F _inst_1 α' β' f as)) (fun (x._@.Mathlib.Control.Traversable.Instances._hyg.1844 : Unit) => Traversable.traverse.{u1} List.{u1} instTraversableList.{u1} F _inst_1 α' β' f bs))
Case conversion may be inaccurate. Consider using '#align list.traverse_append List.traverse_appendₓ'. -/
@[simp]
theorem traverse_append :
    ∀ as bs : List α', traverse f (as ++ bs) = (· ++ ·) <$> traverse f as <*> traverse f bs
  | [], bs => by
    have : Append.append ([] : List β') = id := by funext <;> rfl
    simp [this, functor_norm]
  | a :: as, bs => by simp [traverse_append as bs, functor_norm] <;> congr
#align list.traverse_append List.traverse_append

#print List.mem_traverse /-
theorem mem_traverse {f : α' → Set β'} :
    ∀ (l : List α') (n : List β'), n ∈ traverse f l ↔ Forall₂ (fun b a => b ∈ f a) n l
  | [], [] => by simp
  | a :: as, [] => by simp
  | [], b :: bs => by simp
  | a :: as, b :: bs => by simp [mem_traverse as bs]
#align list.mem_traverse List.mem_traverse
-/

end Traverse

end List

namespace Sum

section Traverse

variable {σ : Type u}

variable {F G : Type u → Type u}

variable [Applicative F] [Applicative G]

open Applicative Functor

open List (cons)

/- warning: sum.traverse_map -> Sum.traverse_map is a dubious translation:
lean 3 declaration is
  forall {σ : Type.{u1}} {G : Type.{u1} -> Type.{u1}} [_inst_2 : Applicative.{u1, u1} G] {α : Type.{u1}} {β : Type.{u1}} {γ : Type.{u1}} (g : α -> β) (f : β -> (G γ)) (x : Sum.{u1, u1} σ α), Eq.{succ u1} (G (Sum.{u1, u1} σ γ)) (Sum.traverse.{u1, u1} σ G _inst_2 β γ f (Functor.map.{u1, u1} (Sum.{u1, u1} σ) (Traversable.toFunctor.{u1} (Sum.{u1, u1} σ) (Sum.traversable.{u1} σ)) α β g x)) (Sum.traverse.{u1, u1} σ G _inst_2 α γ (Function.comp.{succ u1, succ u1, succ u1} α β (G γ) f g) x)
but is expected to have type
  forall {σ : Type.{u1}} {G : Type.{u1} -> Type.{u1}} [_inst_2 : Applicative.{u1, u1} G] {α : Type.{u1}} {β : Type.{u1}} {γ : Type.{u1}} (g : α -> β) (f : β -> (G γ)) (x : Sum.{u1, u1} σ α), Eq.{succ u1} (G (Sum.{u1, u1} σ γ)) (Sum.traverse.{u1, u1} σ G _inst_2 β γ f (Functor.map.{u1, u1} (Sum.{u1, u1} σ) (Traversable.toFunctor.{u1} (Sum.{u1, u1} σ) (instTraversableSum.{u1} σ)) α β g x)) (Sum.traverse.{u1, u1} σ G _inst_2 α γ (Function.comp.{succ u1, succ u1, succ u1} α β (G γ) f g) x)
Case conversion may be inaccurate. Consider using '#align sum.traverse_map Sum.traverse_mapₓ'. -/
protected theorem traverse_map {α β γ : Type u} (g : α → β) (f : β → G γ) (x : Sum σ α) :
    Sum.traverse f (g <$> x) = Sum.traverse (f ∘ g) x := by
  cases x <;> simp [Sum.traverse, id_map, functor_norm] <;> rfl
#align sum.traverse_map Sum.traverse_map

variable [LawfulApplicative F] [LawfulApplicative G]

/- warning: sum.id_traverse -> Sum.id_traverse is a dubious translation:
lean 3 declaration is
  forall {σ : Type.{u1}} {α : Type.{u1}} (x : Sum.{u1, u1} σ α), Eq.{succ u1} (id.{succ (succ u1)} Type.{u1} (Sum.{u1, u1} σ α)) (Sum.traverse.{u1, u1} σ (id.{succ (succ u1)} Type.{u1}) (Monad.toApplicative.{u1, u1} (id.{succ (succ u1)} Type.{u1}) id.monad.{u1}) α α (id.mk.{succ u1} α) x) x
but is expected to have type
  forall {σ : Type.{u1}} {α : Type.{u1}} (x : Sum.{u1, u1} σ α), Eq.{succ u1} (Id.{u1} (Sum.{u1, u1} σ α)) (Sum.traverse.{u1, u1} σ Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1}) α α (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) α) x) x
Case conversion may be inaccurate. Consider using '#align sum.id_traverse Sum.id_traverseₓ'. -/
protected theorem id_traverse {σ α} (x : Sum σ α) : Sum.traverse id.mk x = x := by cases x <;> rfl
#align sum.id_traverse Sum.id_traverse

/- warning: sum.comp_traverse -> Sum.comp_traverse is a dubious translation:
lean 3 declaration is
  forall {σ : Type.{u}} {F : Type.{u} -> Type.{u}} {G : Type.{u} -> Type.{u}} [_inst_1 : Applicative.{u, u} F] [_inst_2 : Applicative.{u, u} G] [_inst_3 : LawfulApplicative.{u, u} F _inst_1] [_inst_4 : LawfulApplicative.{u, u} G _inst_2] {α : Type.{u_1}} {β : Type.{u}} {γ : Type.{u}} (f : β -> (F γ)) (g : α -> (G β)) (x : Sum.{u, u_1} σ α), Eq.{succ u} (Functor.Comp.{u, u, u} (fun {β : Type.{u}} => G β) F (Sum.{u, u} σ γ)) (Sum.traverse.{u, u_1} σ (Functor.Comp.{u, u, u} (fun {β : Type.{u}} => G β) F) (Functor.Comp.applicative.{u, u, u} (fun {β : Type.{u}} => G β) F _inst_2 _inst_1) α γ (Function.comp.{succ u_1, succ u, succ u} α (G (F γ)) (Functor.Comp.{u, u, u} (fun {β : Type.{u}} => G β) F γ) (Functor.Comp.mk.{u, u, u} (fun {β : Type.{u}} => G β) F γ) (Function.comp.{succ u_1, succ u, succ u} α (G β) (G (F γ)) (Functor.map.{u, u} (fun {β : Type.{u}} => G β) (Applicative.toFunctor.{u, u} (fun {β : Type.{u}} => G β) _inst_2) β (F γ) f) g)) x) (Functor.Comp.mk.{u, u, u} (fun {β : Type.{u}} => G β) F (Sum.{u, u} σ γ) (Functor.map.{u, u} G (Applicative.toFunctor.{u, u} G _inst_2) (Sum.{u, u} σ β) (F (Sum.{u, u} σ γ)) (Sum.traverse.{u, u} σ F _inst_1 β γ f) (Sum.traverse.{u, u_1} σ G _inst_2 α β g x)))
but is expected to have type
  forall {σ : Type.{u}} {F : Type.{u} -> Type.{u}} {G : Type.{u} -> Type.{u}} [_inst_1 : Applicative.{u, u} F] [_inst_2 : Applicative.{u, u} G] [_inst_3 : LawfulApplicative.{u, u} G _inst_2] {_inst_4 : Type.{u}} {α : Type.{u}} {β : Type.{u}} (γ : α -> (F β)) (f : _inst_4 -> (G α)) (g : Sum.{u, u} σ _inst_4), Eq.{succ u} (Functor.Comp.{u, u, u} G F (Sum.{u, u} σ β)) (Sum.traverse.{u, u} σ (Functor.Comp.{u, u, u} G F) (Functor.Comp.instApplicativeComp.{u, u, u} G F _inst_2 _inst_1) _inst_4 β (Function.comp.{succ u, succ u, succ u} _inst_4 (G (F β)) (Functor.Comp.{u, u, u} G F β) (Functor.Comp.mk.{u, u, u} G F β) (Function.comp.{succ u, succ u, succ u} _inst_4 (G α) (G (F β)) ((fun (x._@.Mathlib.Control.Traversable.Instances._hyg.2374 : α -> (F β)) (x._@.Mathlib.Control.Traversable.Instances._hyg.2376 : G α) => Functor.map.{u, u} G (Applicative.toFunctor.{u, u} G _inst_2) α (F β) x._@.Mathlib.Control.Traversable.Instances._hyg.2374 x._@.Mathlib.Control.Traversable.Instances._hyg.2376) γ) f)) g) (Functor.Comp.mk.{u, u, u} G F (Sum.{u, u} σ β) (Functor.map.{u, u} G (Applicative.toFunctor.{u, u} G _inst_2) (Sum.{u, u} σ α) (F (Sum.{u, u} σ β)) (Sum.traverse.{u, u} σ F _inst_1 α β γ) (Sum.traverse.{u, u} σ G _inst_2 _inst_4 α f g)))
Case conversion may be inaccurate. Consider using '#align sum.comp_traverse Sum.comp_traverseₓ'. -/
@[nolint unused_arguments]
protected theorem comp_traverse {α β γ} (f : β → F γ) (g : α → G β) (x : Sum σ α) :
    Sum.traverse (comp.mk ∘ (· <$> ·) f ∘ g) x = Comp.mk (Sum.traverse f <$> Sum.traverse g x) := by
  cases x <;> simp! [Sum.traverse, map_id, functor_norm] <;> rfl
#align sum.comp_traverse Sum.comp_traverse

/- warning: sum.traverse_eq_map_id -> Sum.traverse_eq_map_id is a dubious translation:
lean 3 declaration is
  forall {σ : Type.{u1}} {α : Type.{u1}} {β : Type.{u1}} (f : α -> β) (x : Sum.{u1, u1} σ α), Eq.{succ u1} (id.{succ (succ u1)} Type.{u1} (Sum.{u1, u1} σ β)) (Sum.traverse.{u1, u1} σ (id.{succ (succ u1)} Type.{u1}) (Monad.toApplicative.{u1, u1} (id.{succ (succ u1)} Type.{u1}) id.monad.{u1}) α β (Function.comp.{succ u1, succ u1, succ u1} α β (id.{succ (succ u1)} Type.{u1} β) (id.mk.{succ u1} β) f) x) (id.mk.{succ u1} (Sum.{u1, u1} σ β) (Functor.map.{u1, u1} (Sum.{u1, u1} σ) (Traversable.toFunctor.{u1} (Sum.{u1, u1} σ) (Sum.traversable.{u1} σ)) α β f x))
but is expected to have type
  forall {σ : Type.{u1}} {α : Type.{u1}} {β : Type.{u1}} (f : α -> β) (x : Sum.{u1, u1} σ α), Eq.{succ u1} (Id.{u1} (Sum.{u1, u1} σ β)) (Sum.traverse.{u1, u1} σ Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1}) α β (Function.comp.{succ u1, succ u1, succ u1} α β (Id.{u1} β) (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) β) f) x) (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) (Sum.{u1, u1} σ β) (Functor.map.{u1, u1} (Sum.{u1, u1} σ) (Traversable.toFunctor.{u1} (Sum.{u1, u1} σ) (instTraversableSum.{u1} σ)) α β f x))
Case conversion may be inaccurate. Consider using '#align sum.traverse_eq_map_id Sum.traverse_eq_map_idₓ'. -/
protected theorem traverse_eq_map_id {α β} (f : α → β) (x : Sum σ α) :
    Sum.traverse (id.mk ∘ f) x = id.mk (f <$> x) := by
  induction x <;> simp! [*, functor_norm] <;> rfl
#align sum.traverse_eq_map_id Sum.traverse_eq_map_id

/- warning: sum.map_traverse -> Sum.map_traverse is a dubious translation:
lean 3 declaration is
  forall {σ : Type.{u1}} {G : Type.{u1} -> Type.{u1}} [_inst_2 : Applicative.{u1, u1} G] [_inst_4 : LawfulApplicative.{u1, u1} G _inst_2] {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u1}} (g : α -> (G β)) (f : β -> γ) (x : Sum.{u1, u2} σ α), Eq.{succ u1} (G (Sum.{u1, u1} σ γ)) (Functor.map.{u1, u1} (fun {β : Type.{u1}} => G β) (Applicative.toFunctor.{u1, u1} (fun {β : Type.{u1}} => G β) _inst_2) (Sum.{u1, u1} σ β) (Sum.{u1, u1} σ γ) (Functor.map.{u1, u1} (Sum.{u1, u1} σ) (Traversable.toFunctor.{u1} (Sum.{u1, u1} σ) (Sum.traversable.{u1} σ)) β γ f) (Sum.traverse.{u1, u2} σ (fun {β : Type.{u1}} => G β) _inst_2 α β g x)) (Sum.traverse.{u1, u2} σ G _inst_2 α γ (Function.comp.{succ u2, succ u1, succ u1} α (G β) (G γ) (Functor.map.{u1, u1} G (Applicative.toFunctor.{u1, u1} G _inst_2) β γ f) g) x)
but is expected to have type
  forall {σ : Type.{u2}} {G : Type.{u2} -> Type.{u2}} [_inst_2 : Applicative.{u2, u2} G] [_inst_4 : LawfulApplicative.{u2, u2} G _inst_2] {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u2}} (g : α -> (G β)) (f : β -> γ) (x : Sum.{u2, u1} σ α), Eq.{succ u2} (G (Sum.{u2, u2} σ γ)) (Functor.map.{u2, u2} G (Applicative.toFunctor.{u2, u2} G _inst_2) (Sum.{u2, u2} σ β) (Sum.{u2, u2} σ γ) ((fun (x._@.Mathlib.Control.Traversable.Instances._hyg.2808 : β -> γ) (x._@.Mathlib.Control.Traversable.Instances._hyg.2810 : Sum.{u2, u2} σ β) => Functor.map.{u2, u2} (Sum.{u2, u2} σ) (Traversable.toFunctor.{u2} (Sum.{u2, u2} σ) (instTraversableSum.{u2} σ)) β γ x._@.Mathlib.Control.Traversable.Instances._hyg.2808 x._@.Mathlib.Control.Traversable.Instances._hyg.2810) f) (Sum.traverse.{u2, u1} σ G _inst_2 α β g x)) (Sum.traverse.{u2, u1} σ G _inst_2 α γ (Function.comp.{succ u1, succ u2, succ u2} α (G β) (G γ) ((fun (x._@.Mathlib.Control.Traversable.Instances._hyg.2834 : β -> γ) (x._@.Mathlib.Control.Traversable.Instances._hyg.2836 : G β) => Functor.map.{u2, u2} G (Applicative.toFunctor.{u2, u2} G _inst_2) β γ x._@.Mathlib.Control.Traversable.Instances._hyg.2834 x._@.Mathlib.Control.Traversable.Instances._hyg.2836) f) g) x)
Case conversion may be inaccurate. Consider using '#align sum.map_traverse Sum.map_traverseₓ'. -/
protected theorem map_traverse {α β γ} (g : α → G β) (f : β → γ) (x : Sum σ α) :
    (· <$> ·) f <$> Sum.traverse g x = Sum.traverse ((· <$> ·) f ∘ g) x := by
  cases x <;> simp [Sum.traverse, id_map, functor_norm] <;> congr <;> rfl
#align sum.map_traverse Sum.map_traverse

variable (η : ApplicativeTransformation F G)

/- warning: sum.naturality -> Sum.naturality is a dubious translation:
lean 3 declaration is
  forall {σ : Type.{u1}} {F : Type.{u1} -> Type.{u1}} {G : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} F] [_inst_2 : Applicative.{u1, u1} G] [_inst_3 : LawfulApplicative.{u1, u1} F _inst_1] [_inst_4 : LawfulApplicative.{u1, u1} G _inst_2] (η : ApplicativeTransformation.{u1, u1, u1} F _inst_1 _inst_3 G _inst_2 _inst_4) {α : Type.{u2}} {β : Type.{u1}} (f : α -> (F β)) (x : Sum.{u1, u2} σ α), Eq.{succ u1} (G (Sum.{u1, u1} σ β)) (coeFn.{succ (succ u1), succ (succ u1)} (ApplicativeTransformation.{u1, u1, u1} F _inst_1 _inst_3 G _inst_2 _inst_4) (fun (_x : ApplicativeTransformation.{u1, u1, u1} F _inst_1 _inst_3 G _inst_2 _inst_4) => forall {α : Type.{u1}}, (F α) -> (G α)) (ApplicativeTransformation.hasCoeToFun.{u1, u1, u1} F _inst_1 _inst_3 G _inst_2 _inst_4) η (Sum.{u1, u1} σ β) (Sum.traverse.{u1, u2} σ F _inst_1 α β f x)) (Sum.traverse.{u1, u2} σ G _inst_2 α β (Function.comp.{succ u2, succ u1, succ u1} α (F β) (G β) (coeFn.{succ (succ u1), succ (succ u1)} (ApplicativeTransformation.{u1, u1, u1} F _inst_1 _inst_3 G _inst_2 _inst_4) (fun (_x : ApplicativeTransformation.{u1, u1, u1} F _inst_1 _inst_3 G _inst_2 _inst_4) => forall {α : Type.{u1}}, (F α) -> (G α)) (ApplicativeTransformation.hasCoeToFun.{u1, u1, u1} F _inst_1 _inst_3 G _inst_2 _inst_4) η β) f) x)
but is expected to have type
  forall {σ : Type.{u2}} {F : Type.{u2} -> Type.{u2}} {G : Type.{u2} -> Type.{u2}} [_inst_1 : Applicative.{u2, u2} F] [_inst_2 : Applicative.{u2, u2} G] [_inst_3 : LawfulApplicative.{u2, u2} F _inst_1] [_inst_4 : LawfulApplicative.{u2, u2} G _inst_2] (η : ApplicativeTransformation.{u2, u2, u2} F _inst_1 G _inst_2) {α : Type.{u1}} {β : Type.{u2}} (f : α -> (F β)) (x : Sum.{u2, u1} σ α), Eq.{succ u2} (G (Sum.{u2, u2} σ β)) ((fun {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u2}} => ApplicativeTransformation.app.{u2, u2, u2} F _inst_1 G _inst_2 η α._@.Mathlib.Control.Traversable.Basic._hyg.245) (Sum.{u2, u2} σ β) (Sum.traverse.{u2, u1} σ F _inst_1 α β f x)) (Sum.traverse.{u2, u1} σ G _inst_2 α β (Function.comp.{succ u1, succ u2, succ u2} α (F β) (G β) ((fun {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u2}} => ApplicativeTransformation.app.{u2, u2, u2} F _inst_1 G _inst_2 η α._@.Mathlib.Control.Traversable.Basic._hyg.245) β) f) x)
Case conversion may be inaccurate. Consider using '#align sum.naturality Sum.naturalityₓ'. -/
protected theorem naturality {α β} (f : α → F β) (x : Sum σ α) :
    η (Sum.traverse f x) = Sum.traverse (@η _ ∘ f) x := by
  cases x <;> simp! [Sum.traverse, functor_norm]
#align sum.naturality Sum.naturality

end Traverse

instance {σ : Type u} : IsLawfulTraversable.{u} (Sum σ) :=
  { Sum.lawfulMonad with
    id_traverse := @Sum.id_traverse σ
    comp_traverse := @Sum.comp_traverse σ
    traverse_eq_map_id := @Sum.traverse_eq_map_id σ
    naturality := @Sum.naturality σ }

end Sum

