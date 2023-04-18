/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module control.bitraversable.lemmas
! leanprover-community/mathlib commit 58581d0fe523063f5651df0619be2bf65012a94a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Control.Bitraversable.Basic

/-!
# Bitraversable Lemmas

## Main definitions
  * tfst - traverse on first functor argument
  * tsnd - traverse on second functor argument

## Lemmas

Combination of
  * bitraverse
  * tfst
  * tsnd

with the applicatives `id` and `comp`

## References

 * Hackage: <https://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Bitraversable.html>

## Tags

traversable bitraversable functor bifunctor applicative


-/


universe u

variable {t : Type u → Type u → Type u} [Bitraversable t]

variable {β : Type u}

namespace Bitraversable

open Functor LawfulApplicative

variable {F G : Type u → Type u} [Applicative F] [Applicative G]

#print Bitraversable.tfst /-
/-- traverse on the first functor argument -/
@[reducible]
def tfst {α α'} (f : α → F α') : t α β → F (t α' β) :=
  bitraverse f pure
#align bitraversable.tfst Bitraversable.tfst
-/

#print Bitraversable.tsnd /-
/-- traverse on the second functor argument -/
@[reducible]
def tsnd {α α'} (f : α → F α') : t β α → F (t β α') :=
  bitraverse pure f
#align bitraversable.tsnd Bitraversable.tsnd
-/

variable [IsLawfulBitraversable t] [LawfulApplicative F] [LawfulApplicative G]

/- warning: bitraversable.id_tfst -> Bitraversable.id_tfst is a dubious translation:
lean 3 declaration is
  forall {t : Type.{u1} -> Type.{u1} -> Type.{u1}} [_inst_1 : Bitraversable.{u1} t] [_inst_4 : IsLawfulBitraversable.{u1} t _inst_1] {α : Type.{u1}} {β : Type.{u1}} (x : t α β), Eq.{succ u1} (id.{succ (succ u1)} Type.{u1} (t α β)) (Bitraversable.tfst.{u1} t _inst_1 β (id.{succ (succ u1)} Type.{u1}) (Monad.toApplicative.{u1, u1} (id.{succ (succ u1)} Type.{u1}) id.monad.{u1}) α α (id.mk.{succ u1} α) x) (id.mk.{succ u1} (t α β) x)
but is expected to have type
  forall {t : Type.{u1} -> Type.{u1} -> Type.{u1}} [_inst_1 : Bitraversable.{u1} t] [_inst_4 : IsLawfulBitraversable.{u1} t _inst_1] {α : Type.{u1}} {β : Type.{u1}} (x : t α β), Eq.{succ u1} (Id.{u1} (t α β)) (Bitraversable.tfst.{u1} t _inst_1 β Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1}) α α (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) α) x) (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) (t α β) x)
Case conversion may be inaccurate. Consider using '#align bitraversable.id_tfst Bitraversable.id_tfstₓ'. -/
@[higher_order.1tfst_id]
theorem id_tfst : ∀ {α β} (x : t α β), tfst id.mk x = id.mk x :=
  @id_bitraverse _ _ _
#align bitraversable.id_tfst Bitraversable.id_tfst

/- warning: bitraversable.id_tsnd -> Bitraversable.id_tsnd is a dubious translation:
lean 3 declaration is
  forall {t : Type.{u1} -> Type.{u1} -> Type.{u1}} [_inst_1 : Bitraversable.{u1} t] [_inst_4 : IsLawfulBitraversable.{u1} t _inst_1] {α : Type.{u1}} {β : Type.{u1}} (x : t α β), Eq.{succ u1} (id.{succ (succ u1)} Type.{u1} (t α β)) (Bitraversable.tsnd.{u1} t _inst_1 α (id.{succ (succ u1)} Type.{u1}) (Monad.toApplicative.{u1, u1} (id.{succ (succ u1)} Type.{u1}) id.monad.{u1}) β β (id.mk.{succ u1} β) x) (id.mk.{succ u1} (t α β) x)
but is expected to have type
  forall {t : Type.{u1} -> Type.{u1} -> Type.{u1}} [_inst_1 : Bitraversable.{u1} t] [_inst_4 : IsLawfulBitraversable.{u1} t _inst_1] {α : Type.{u1}} {β : Type.{u1}} (x : t α β), Eq.{succ u1} (Id.{u1} (t α β)) (Bitraversable.tsnd.{u1} t _inst_1 α Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1}) β β (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) β) x) (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) (t α β) x)
Case conversion may be inaccurate. Consider using '#align bitraversable.id_tsnd Bitraversable.id_tsndₓ'. -/
@[higher_order.1tsnd_id]
theorem id_tsnd : ∀ {α β} (x : t α β), tsnd id.mk x = id.mk x :=
  @id_bitraverse _ _ _
#align bitraversable.id_tsnd Bitraversable.id_tsnd

/- warning: bitraversable.comp_tfst -> Bitraversable.comp_tfst is a dubious translation:
lean 3 declaration is
  forall {t : Type.{u1} -> Type.{u1} -> Type.{u1}} [_inst_1 : Bitraversable.{u1} t] {F : Type.{u1} -> Type.{u1}} {G : Type.{u1} -> Type.{u1}} [_inst_2 : Applicative.{u1, u1} F] [_inst_3 : Applicative.{u1, u1} G] [_inst_4 : IsLawfulBitraversable.{u1} t _inst_1] [_inst_5 : LawfulApplicative.{u1, u1} F _inst_2] [_inst_6 : LawfulApplicative.{u1, u1} G _inst_3] {α₀ : Type.{u1}} {α₁ : Type.{u1}} {α₂ : Type.{u1}} {β : Type.{u1}} (f : α₀ -> (F α₁)) (f' : α₁ -> (G α₂)) (x : t α₀ β), Eq.{succ u1} (Functor.Comp.{u1, u1, u1} (fun {α₁ : Type.{u1}} => F α₁) G (t α₂ β)) (Functor.Comp.mk.{u1, u1, u1} (fun {α₁ : Type.{u1}} => F α₁) G (t α₂ β) (Functor.map.{u1, u1} (fun {α₁ : Type.{u1}} => F α₁) (Applicative.toFunctor.{u1, u1} (fun {α₁ : Type.{u1}} => F α₁) _inst_2) (t α₁ β) (G (t α₂ β)) (Bitraversable.tfst.{u1} t _inst_1 β G _inst_3 α₁ α₂ f') (Bitraversable.tfst.{u1} t _inst_1 β (fun {α₁ : Type.{u1}} => F α₁) _inst_2 α₀ α₁ f x))) (Bitraversable.tfst.{u1} t _inst_1 β (Functor.Comp.{u1, u1, u1} (fun {α₁ : Type.{u1}} => F α₁) G) (Functor.Comp.applicative.{u1, u1, u1} (fun {α₁ : Type.{u1}} => F α₁) G _inst_2 _inst_3) α₀ α₂ (Function.comp.{succ u1, succ u1, succ u1} α₀ (F (G α₂)) (Functor.Comp.{u1, u1, u1} (fun {α₁ : Type.{u1}} => F α₁) G α₂) (Functor.Comp.mk.{u1, u1, u1} (fun {α₁ : Type.{u1}} => F α₁) G α₂) (Function.comp.{succ u1, succ u1, succ u1} α₀ (F α₁) (F (G α₂)) (Functor.map.{u1, u1} F (Applicative.toFunctor.{u1, u1} F _inst_2) α₁ (G α₂) f') f)) x)
but is expected to have type
  forall {t : Type.{u1} -> Type.{u1} -> Type.{u1}} [_inst_1 : Bitraversable.{u1} t] {F : Type.{u1} -> Type.{u1}} {G : Type.{u1} -> Type.{u1}} [_inst_2 : Applicative.{u1, u1} F] [_inst_3 : Applicative.{u1, u1} G] [_inst_4 : IsLawfulBitraversable.{u1} t _inst_1] [_inst_5 : LawfulApplicative.{u1, u1} F _inst_2] [_inst_6 : LawfulApplicative.{u1, u1} G _inst_3] {α₀ : Type.{u1}} {α₁ : Type.{u1}} {α₂ : Type.{u1}} {β : Type.{u1}} (f : α₀ -> (F α₁)) (f' : α₁ -> (G α₂)) (x : t α₀ β), Eq.{succ u1} (Functor.Comp.{u1, u1, u1} F G (t α₂ β)) (Functor.Comp.mk.{u1, u1, u1} F G (t α₂ β) (Functor.map.{u1, u1} F (Applicative.toFunctor.{u1, u1} F _inst_2) (t α₁ β) (G (t α₂ β)) (Bitraversable.tfst.{u1} t _inst_1 β G _inst_3 α₁ α₂ f') (Bitraversable.tfst.{u1} t _inst_1 β F _inst_2 α₀ α₁ f x))) (Bitraversable.tfst.{u1} t _inst_1 β (Functor.Comp.{u1, u1, u1} F G) (Functor.Comp.instApplicativeComp.{u1, u1, u1} F G _inst_2 _inst_3) α₀ α₂ (Function.comp.{succ u1, succ u1, succ u1} α₀ (F (G α₂)) (Functor.Comp.{u1, u1, u1} F G α₂) (Functor.Comp.mk.{u1, u1, u1} F G α₂) (Function.comp.{succ u1, succ u1, succ u1} α₀ (F α₁) (F (G α₂)) (Functor.map.{u1, u1} F (Applicative.toFunctor.{u1, u1} F _inst_2) α₁ (G α₂) f') f)) x)
Case conversion may be inaccurate. Consider using '#align bitraversable.comp_tfst Bitraversable.comp_tfstₓ'. -/
@[higher_order.1tfst_comp_tfst]
theorem comp_tfst {α₀ α₁ α₂ β} (f : α₀ → F α₁) (f' : α₁ → G α₂) (x : t α₀ β) :
    Comp.mk (tfst f' <$> tfst f x) = tfst (Comp.mk ∘ map f' ∘ f) x := by
  rw [← comp_bitraverse] <;> simp [tfst, map_comp_pure, Pure.pure]
#align bitraversable.comp_tfst Bitraversable.comp_tfst

/- warning: bitraversable.tfst_tsnd -> Bitraversable.tfst_tsnd is a dubious translation:
lean 3 declaration is
  forall {t : Type.{u1} -> Type.{u1} -> Type.{u1}} [_inst_1 : Bitraversable.{u1} t] {F : Type.{u1} -> Type.{u1}} {G : Type.{u1} -> Type.{u1}} [_inst_2 : Applicative.{u1, u1} F] [_inst_3 : Applicative.{u1, u1} G] [_inst_4 : IsLawfulBitraversable.{u1} t _inst_1] [_inst_5 : LawfulApplicative.{u1, u1} F _inst_2] [_inst_6 : LawfulApplicative.{u1, u1} G _inst_3] {α₀ : Type.{u1}} {α₁ : Type.{u1}} {β₀ : Type.{u1}} {β₁ : Type.{u1}} (f : α₀ -> (F α₁)) (f' : β₀ -> (G β₁)) (x : t α₀ β₀), Eq.{succ u1} (Functor.Comp.{u1, u1, u1} G F (t α₁ β₁)) (Functor.Comp.mk.{u1, u1, u1} G F (t α₁ β₁) (Functor.map.{u1, u1} G (Applicative.toFunctor.{u1, u1} G _inst_3) (t α₀ β₁) (F (t α₁ β₁)) (Bitraversable.tfst.{u1} (fun {α₀ : Type.{u1}} {β₀ : Type.{u1}} => t α₀ β₀) _inst_1 β₁ F _inst_2 α₀ α₁ f) (Bitraversable.tsnd.{u1} (fun {α₀ : Type.{u1}} {β₀ : Type.{u1}} => t α₀ β₀) _inst_1 α₀ G _inst_3 β₀ β₁ f' x))) (Bitraversable.bitraverse.{u1} t _inst_1 (Functor.Comp.{u1, u1, u1} G F) (Functor.Comp.applicative.{u1, u1, u1} G F _inst_3 _inst_2) α₀ α₁ β₀ β₁ (Function.comp.{succ u1, succ u1, succ u1} α₀ (G (F α₁)) (Functor.Comp.{u1, u1, u1} G F α₁) (Functor.Comp.mk.{u1, u1, u1} G F α₁) (Function.comp.{succ u1, succ u1, succ u1} α₀ (F α₁) (G (F α₁)) (Pure.pure.{u1, u1} G (Applicative.toHasPure.{u1, u1} G _inst_3) (F α₁)) f)) (Function.comp.{succ u1, succ u1, succ u1} β₀ (G (F β₁)) (Functor.Comp.{u1, u1, u1} G F β₁) (Functor.Comp.mk.{u1, u1, u1} G F β₁) (Function.comp.{succ u1, succ u1, succ u1} β₀ (G β₁) (G (F β₁)) (Functor.map.{u1, u1} G (Applicative.toFunctor.{u1, u1} G _inst_3) β₁ (F β₁) (Pure.pure.{u1, u1} F (Applicative.toHasPure.{u1, u1} F _inst_2) β₁)) f')) x)
but is expected to have type
  forall {t : Type.{u1} -> Type.{u1} -> Type.{u1}} [_inst_1 : Bitraversable.{u1} t] {F : Type.{u1} -> Type.{u1}} {G : Type.{u1} -> Type.{u1}} [_inst_2 : Applicative.{u1, u1} F] [_inst_3 : Applicative.{u1, u1} G] [_inst_4 : IsLawfulBitraversable.{u1} t _inst_1] [_inst_5 : LawfulApplicative.{u1, u1} F _inst_2] [_inst_6 : LawfulApplicative.{u1, u1} G _inst_3] {α₀ : Type.{u1}} {α₁ : Type.{u1}} {β₀ : Type.{u1}} {β₁ : Type.{u1}} (f : α₀ -> (F α₁)) (f' : β₀ -> (G β₁)) (x : t α₀ β₀), Eq.{succ u1} (Functor.Comp.{u1, u1, u1} G F (t α₁ β₁)) (Functor.Comp.mk.{u1, u1, u1} G F (t α₁ β₁) (Functor.map.{u1, u1} G (Applicative.toFunctor.{u1, u1} G _inst_3) (t α₀ β₁) (F (t α₁ β₁)) (Bitraversable.tfst.{u1} t _inst_1 β₁ F _inst_2 α₀ α₁ f) (Bitraversable.tsnd.{u1} t _inst_1 α₀ G _inst_3 β₀ β₁ f' x))) (Bitraversable.bitraverse.{u1} t _inst_1 (Functor.Comp.{u1, u1, u1} G F) (Functor.Comp.instApplicativeComp.{u1, u1, u1} G F _inst_3 _inst_2) α₀ α₁ β₀ β₁ (Function.comp.{succ u1, succ u1, succ u1} α₀ (G (F α₁)) (Functor.Comp.{u1, u1, u1} G F α₁) (Functor.Comp.mk.{u1, u1, u1} G F α₁) (Function.comp.{succ u1, succ u1, succ u1} α₀ (F α₁) (G (F α₁)) (Pure.pure.{u1, u1} G (Applicative.toPure.{u1, u1} G _inst_3) (F α₁)) f)) (Function.comp.{succ u1, succ u1, succ u1} β₀ (G (F β₁)) (Functor.Comp.{u1, u1, u1} G F β₁) (Functor.Comp.mk.{u1, u1, u1} G F β₁) (Function.comp.{succ u1, succ u1, succ u1} β₀ (G β₁) (G (F β₁)) (Functor.map.{u1, u1} G (Applicative.toFunctor.{u1, u1} G _inst_3) β₁ (F β₁) (Pure.pure.{u1, u1} F (Applicative.toPure.{u1, u1} F _inst_2) β₁)) f')) x)
Case conversion may be inaccurate. Consider using '#align bitraversable.tfst_tsnd Bitraversable.tfst_tsndₓ'. -/
@[higher_order.1tfst_comp_tsnd]
theorem tfst_tsnd {α₀ α₁ β₀ β₁} (f : α₀ → F α₁) (f' : β₀ → G β₁) (x : t α₀ β₀) :
    Comp.mk (tfst f <$> tsnd f' x) = bitraverse (Comp.mk ∘ pure ∘ f) (Comp.mk ∘ map pure ∘ f') x :=
  by rw [← comp_bitraverse] <;> simp [tfst, tsnd]
#align bitraversable.tfst_tsnd Bitraversable.tfst_tsnd

/- warning: bitraversable.tsnd_tfst -> Bitraversable.tsnd_tfst is a dubious translation:
lean 3 declaration is
  forall {t : Type.{u1} -> Type.{u1} -> Type.{u1}} [_inst_1 : Bitraversable.{u1} t] {F : Type.{u1} -> Type.{u1}} {G : Type.{u1} -> Type.{u1}} [_inst_2 : Applicative.{u1, u1} F] [_inst_3 : Applicative.{u1, u1} G] [_inst_4 : IsLawfulBitraversable.{u1} t _inst_1] [_inst_5 : LawfulApplicative.{u1, u1} F _inst_2] [_inst_6 : LawfulApplicative.{u1, u1} G _inst_3] {α₀ : Type.{u1}} {α₁ : Type.{u1}} {β₀ : Type.{u1}} {β₁ : Type.{u1}} (f : α₀ -> (F α₁)) (f' : β₀ -> (G β₁)) (x : t α₀ β₀), Eq.{succ u1} (Functor.Comp.{u1, u1, u1} F G (t α₁ β₁)) (Functor.Comp.mk.{u1, u1, u1} F G (t α₁ β₁) (Functor.map.{u1, u1} F (Applicative.toFunctor.{u1, u1} F _inst_2) (t α₁ β₀) (G (t α₁ β₁)) (Bitraversable.tsnd.{u1} (fun {α₀ : Type.{u1}} {β₀ : Type.{u1}} => t α₀ β₀) _inst_1 α₁ G _inst_3 β₀ β₁ f') (Bitraversable.tfst.{u1} (fun {α₀ : Type.{u1}} {β₀ : Type.{u1}} => t α₀ β₀) _inst_1 β₀ F _inst_2 α₀ α₁ f x))) (Bitraversable.bitraverse.{u1} t _inst_1 (Functor.Comp.{u1, u1, u1} F G) (Functor.Comp.applicative.{u1, u1, u1} F G _inst_2 _inst_3) α₀ α₁ β₀ β₁ (Function.comp.{succ u1, succ u1, succ u1} α₀ (F (G α₁)) (Functor.Comp.{u1, u1, u1} F G α₁) (Functor.Comp.mk.{u1, u1, u1} F G α₁) (Function.comp.{succ u1, succ u1, succ u1} α₀ (F α₁) (F (G α₁)) (Functor.map.{u1, u1} F (Applicative.toFunctor.{u1, u1} F _inst_2) α₁ (G α₁) (Pure.pure.{u1, u1} G (Applicative.toHasPure.{u1, u1} G _inst_3) α₁)) f)) (Function.comp.{succ u1, succ u1, succ u1} β₀ (F (G β₁)) (Functor.Comp.{u1, u1, u1} F G β₁) (Functor.Comp.mk.{u1, u1, u1} F G β₁) (Function.comp.{succ u1, succ u1, succ u1} β₀ (G β₁) (F (G β₁)) (Pure.pure.{u1, u1} F (Applicative.toHasPure.{u1, u1} F _inst_2) (G β₁)) f')) x)
but is expected to have type
  forall {t : Type.{u1} -> Type.{u1} -> Type.{u1}} [_inst_1 : Bitraversable.{u1} t] {F : Type.{u1} -> Type.{u1}} {G : Type.{u1} -> Type.{u1}} [_inst_2 : Applicative.{u1, u1} F] [_inst_3 : Applicative.{u1, u1} G] [_inst_4 : IsLawfulBitraversable.{u1} t _inst_1] [_inst_5 : LawfulApplicative.{u1, u1} F _inst_2] [_inst_6 : LawfulApplicative.{u1, u1} G _inst_3] {α₀ : Type.{u1}} {α₁ : Type.{u1}} {β₀ : Type.{u1}} {β₁ : Type.{u1}} (f : α₀ -> (F α₁)) (f' : β₀ -> (G β₁)) (x : t α₀ β₀), Eq.{succ u1} (Functor.Comp.{u1, u1, u1} F G (t α₁ β₁)) (Functor.Comp.mk.{u1, u1, u1} F G (t α₁ β₁) (Functor.map.{u1, u1} F (Applicative.toFunctor.{u1, u1} F _inst_2) (t α₁ β₀) (G (t α₁ β₁)) (Bitraversable.tsnd.{u1} t _inst_1 α₁ G _inst_3 β₀ β₁ f') (Bitraversable.tfst.{u1} t _inst_1 β₀ F _inst_2 α₀ α₁ f x))) (Bitraversable.bitraverse.{u1} t _inst_1 (Functor.Comp.{u1, u1, u1} F G) (Functor.Comp.instApplicativeComp.{u1, u1, u1} F G _inst_2 _inst_3) α₀ α₁ β₀ β₁ (Function.comp.{succ u1, succ u1, succ u1} α₀ (F (G α₁)) (Functor.Comp.{u1, u1, u1} F G α₁) (Functor.Comp.mk.{u1, u1, u1} F G α₁) (Function.comp.{succ u1, succ u1, succ u1} α₀ (F α₁) (F (G α₁)) (Functor.map.{u1, u1} F (Applicative.toFunctor.{u1, u1} F _inst_2) α₁ (G α₁) (Pure.pure.{u1, u1} G (Applicative.toPure.{u1, u1} G _inst_3) α₁)) f)) (Function.comp.{succ u1, succ u1, succ u1} β₀ (F (G β₁)) (Functor.Comp.{u1, u1, u1} F G β₁) (Functor.Comp.mk.{u1, u1, u1} F G β₁) (Function.comp.{succ u1, succ u1, succ u1} β₀ (G β₁) (F (G β₁)) (Pure.pure.{u1, u1} F (Applicative.toPure.{u1, u1} F _inst_2) (G β₁)) f')) x)
Case conversion may be inaccurate. Consider using '#align bitraversable.tsnd_tfst Bitraversable.tsnd_tfstₓ'. -/
@[higher_order.1tsnd_comp_tfst]
theorem tsnd_tfst {α₀ α₁ β₀ β₁} (f : α₀ → F α₁) (f' : β₀ → G β₁) (x : t α₀ β₀) :
    Comp.mk (tsnd f' <$> tfst f x) = bitraverse (Comp.mk ∘ map pure ∘ f) (Comp.mk ∘ pure ∘ f') x :=
  by rw [← comp_bitraverse] <;> simp [tfst, tsnd]
#align bitraversable.tsnd_tfst Bitraversable.tsnd_tfst

/- warning: bitraversable.comp_tsnd -> Bitraversable.comp_tsnd is a dubious translation:
lean 3 declaration is
  forall {t : Type.{u1} -> Type.{u1} -> Type.{u1}} [_inst_1 : Bitraversable.{u1} t] {F : Type.{u1} -> Type.{u1}} {G : Type.{u1} -> Type.{u1}} [_inst_2 : Applicative.{u1, u1} F] [_inst_3 : Applicative.{u1, u1} G] [_inst_4 : IsLawfulBitraversable.{u1} t _inst_1] [_inst_5 : LawfulApplicative.{u1, u1} F _inst_2] [_inst_6 : LawfulApplicative.{u1, u1} G _inst_3] {α : Type.{u1}} {β₀ : Type.{u1}} {β₁ : Type.{u1}} {β₂ : Type.{u1}} (g : β₀ -> (F β₁)) (g' : β₁ -> (G β₂)) (x : t α β₀), Eq.{succ u1} (Functor.Comp.{u1, u1, u1} (fun {β₁ : Type.{u1}} => F β₁) G (t α β₂)) (Functor.Comp.mk.{u1, u1, u1} (fun {β₁ : Type.{u1}} => F β₁) G (t α β₂) (Functor.map.{u1, u1} (fun {β₁ : Type.{u1}} => F β₁) (Applicative.toFunctor.{u1, u1} (fun {β₁ : Type.{u1}} => F β₁) _inst_2) (t α β₁) (G (t α β₂)) (Bitraversable.tsnd.{u1} t _inst_1 α G _inst_3 β₁ β₂ g') (Bitraversable.tsnd.{u1} t _inst_1 α (fun {β₁ : Type.{u1}} => F β₁) _inst_2 β₀ β₁ g x))) (Bitraversable.tsnd.{u1} t _inst_1 α (Functor.Comp.{u1, u1, u1} (fun {β₁ : Type.{u1}} => F β₁) G) (Functor.Comp.applicative.{u1, u1, u1} (fun {β₁ : Type.{u1}} => F β₁) G _inst_2 _inst_3) β₀ β₂ (Function.comp.{succ u1, succ u1, succ u1} β₀ (F (G β₂)) (Functor.Comp.{u1, u1, u1} (fun {β₁ : Type.{u1}} => F β₁) G β₂) (Functor.Comp.mk.{u1, u1, u1} (fun {β₁ : Type.{u1}} => F β₁) G β₂) (Function.comp.{succ u1, succ u1, succ u1} β₀ (F β₁) (F (G β₂)) (Functor.map.{u1, u1} F (Applicative.toFunctor.{u1, u1} F _inst_2) β₁ (G β₂) g') g)) x)
but is expected to have type
  forall {t : Type.{u1} -> Type.{u1} -> Type.{u1}} [_inst_1 : Bitraversable.{u1} t] {F : Type.{u1} -> Type.{u1}} {G : Type.{u1} -> Type.{u1}} [_inst_2 : Applicative.{u1, u1} F] [_inst_3 : Applicative.{u1, u1} G] [_inst_4 : IsLawfulBitraversable.{u1} t _inst_1] [_inst_5 : LawfulApplicative.{u1, u1} F _inst_2] [_inst_6 : LawfulApplicative.{u1, u1} G _inst_3] {α : Type.{u1}} {β₀ : Type.{u1}} {β₁ : Type.{u1}} {β₂ : Type.{u1}} (g : β₀ -> (F β₁)) (g' : β₁ -> (G β₂)) (x : t α β₀), Eq.{succ u1} (Functor.Comp.{u1, u1, u1} F G (t α β₂)) (Functor.Comp.mk.{u1, u1, u1} F G (t α β₂) (Functor.map.{u1, u1} F (Applicative.toFunctor.{u1, u1} F _inst_2) (t α β₁) (G (t α β₂)) (Bitraversable.tsnd.{u1} t _inst_1 α G _inst_3 β₁ β₂ g') (Bitraversable.tsnd.{u1} t _inst_1 α F _inst_2 β₀ β₁ g x))) (Bitraversable.tsnd.{u1} t _inst_1 α (Functor.Comp.{u1, u1, u1} F G) (Functor.Comp.instApplicativeComp.{u1, u1, u1} F G _inst_2 _inst_3) β₀ β₂ (Function.comp.{succ u1, succ u1, succ u1} β₀ (F (G β₂)) (Functor.Comp.{u1, u1, u1} F G β₂) (Functor.Comp.mk.{u1, u1, u1} F G β₂) (Function.comp.{succ u1, succ u1, succ u1} β₀ (F β₁) (F (G β₂)) (Functor.map.{u1, u1} F (Applicative.toFunctor.{u1, u1} F _inst_2) β₁ (G β₂) g') g)) x)
Case conversion may be inaccurate. Consider using '#align bitraversable.comp_tsnd Bitraversable.comp_tsndₓ'. -/
@[higher_order.1tsnd_comp_tsnd]
theorem comp_tsnd {α β₀ β₁ β₂} (g : β₀ → F β₁) (g' : β₁ → G β₂) (x : t α β₀) :
    Comp.mk (tsnd g' <$> tsnd g x) = tsnd (Comp.mk ∘ map g' ∘ g) x := by
  rw [← comp_bitraverse] <;> simp [tsnd] <;> rfl
#align bitraversable.comp_tsnd Bitraversable.comp_tsnd

open Bifunctor

private theorem pure_eq_id_mk_comp_id {α} : pure = id.mk ∘ @id α :=
  rfl
#align bitraversable.pure_eq_id_mk_comp_id bitraversable.pure_eq_id_mk_comp_id

open Function

/- warning: bitraversable.tfst_eq_fst_id -> Bitraversable.tfst_eq_fst_id is a dubious translation:
lean 3 declaration is
  forall {t : Type.{u1} -> Type.{u1} -> Type.{u1}} [_inst_1 : Bitraversable.{u1} t] [_inst_4 : IsLawfulBitraversable.{u1} t _inst_1] {α : Type.{u1}} {α' : Type.{u1}} {β : Type.{u1}} (f : α -> α') (x : t α β), Eq.{succ u1} (id.{succ (succ u1)} Type.{u1} (t α' β)) (Bitraversable.tfst.{u1} t _inst_1 β (id.{succ (succ u1)} Type.{u1}) (Monad.toApplicative.{u1, u1} (id.{succ (succ u1)} Type.{u1}) id.monad.{u1}) α α' (Function.comp.{succ u1, succ u1, succ u1} α α' (id.{succ (succ u1)} Type.{u1} α') (id.mk.{succ u1} α') f) x) (id.mk.{succ u1} (t α' β) (Bifunctor.fst.{u1, u1, u1} t (Bitraversable.toBifunctor.{u1} t _inst_1) α α' β f x))
but is expected to have type
  forall {t : Type.{u1} -> Type.{u1} -> Type.{u1}} [_inst_1 : Bitraversable.{u1} t] [_inst_4 : IsLawfulBitraversable.{u1} t _inst_1] {α : Type.{u1}} {α' : Type.{u1}} {β : Type.{u1}} (f : α -> α') (x : t α β), Eq.{succ u1} (Id.{u1} (t α' β)) (Bitraversable.tfst.{u1} t _inst_1 β Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1}) α α' (Function.comp.{succ u1, succ u1, succ u1} α α' (Id.{u1} α') (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) α') f) x) (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) (t α' β) (Bifunctor.fst.{u1, u1, u1} t (Bitraversable.toBifunctor.{u1} t _inst_1) α α' β f x))
Case conversion may be inaccurate. Consider using '#align bitraversable.tfst_eq_fst_id Bitraversable.tfst_eq_fst_idₓ'. -/
@[higher_order.1]
theorem tfst_eq_fst_id {α α' β} (f : α → α') (x : t α β) : tfst (id.mk ∘ f) x = id.mk (fst f x) :=
  by simp [tfst, fst, pure_eq_id_mk_comp_id, -comp.right_id, bitraverse_eq_bimap_id]
#align bitraversable.tfst_eq_fst_id Bitraversable.tfst_eq_fst_id

/- warning: bitraversable.tsnd_eq_snd_id -> Bitraversable.tsnd_eq_snd_id is a dubious translation:
lean 3 declaration is
  forall {t : Type.{u1} -> Type.{u1} -> Type.{u1}} [_inst_1 : Bitraversable.{u1} t] [_inst_4 : IsLawfulBitraversable.{u1} t _inst_1] {α : Type.{u1}} {β : Type.{u1}} {β' : Type.{u1}} (f : β -> β') (x : t α β), Eq.{succ u1} (id.{succ (succ u1)} Type.{u1} (t α β')) (Bitraversable.tsnd.{u1} t _inst_1 α (id.{succ (succ u1)} Type.{u1}) (Monad.toApplicative.{u1, u1} (id.{succ (succ u1)} Type.{u1}) id.monad.{u1}) β β' (Function.comp.{succ u1, succ u1, succ u1} β β' (id.{succ (succ u1)} Type.{u1} β') (id.mk.{succ u1} β') f) x) (id.mk.{succ u1} (t α β') (Bifunctor.snd.{u1, u1, u1} t (Bitraversable.toBifunctor.{u1} t _inst_1) α β β' f x))
but is expected to have type
  forall {t : Type.{u1} -> Type.{u1} -> Type.{u1}} [_inst_1 : Bitraversable.{u1} t] [_inst_4 : IsLawfulBitraversable.{u1} t _inst_1] {α : Type.{u1}} {β : Type.{u1}} {β' : Type.{u1}} (f : β -> β') (x : t α β), Eq.{succ u1} (Id.{u1} (t α β')) (Bitraversable.tsnd.{u1} t _inst_1 α Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1}) β β' (Function.comp.{succ u1, succ u1, succ u1} β β' (Id.{u1} β') (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) β') f) x) (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) (t α β') (Bifunctor.snd.{u1, u1, u1} t (Bitraversable.toBifunctor.{u1} t _inst_1) α β β' f x))
Case conversion may be inaccurate. Consider using '#align bitraversable.tsnd_eq_snd_id Bitraversable.tsnd_eq_snd_idₓ'. -/
@[higher_order.1]
theorem tsnd_eq_snd_id {α β β'} (f : β → β') (x : t α β) : tsnd (id.mk ∘ f) x = id.mk (snd f x) :=
  by simp [tsnd, snd, pure_eq_id_mk_comp_id, -comp.right_id, bitraverse_eq_bimap_id]
#align bitraversable.tsnd_eq_snd_id Bitraversable.tsnd_eq_snd_id

attribute [functor_norm]
  comp_bitraverse comp_tsnd comp_tfst tsnd_comp_tsnd tsnd_comp_tfst tfst_comp_tsnd tfst_comp_tfst bitraverse_comp bitraverse_id_id tfst_id tsnd_id

end Bitraversable

