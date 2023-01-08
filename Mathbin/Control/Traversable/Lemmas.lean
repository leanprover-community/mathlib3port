/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module control.traversable.lemmas
! leanprover-community/mathlib commit 940d371319c6658e526349d2c3e1daeeabfae0fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Control.Applicative
import Mathbin.Control.Traversable.Basic

/-!
# Traversing collections

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves basic properties of traversable and applicative functors and defines
`pure_transformation F`, the natural applicative transformation from the identity functor to `F`.

## References

Inspired by [The Essence of the Iterator Pattern][gibbons2009].
-/


universe u

open IsLawfulTraversable

open Function hiding comp

open Functor

attribute [functor_norm] IsLawfulTraversable.naturality

attribute [simp] IsLawfulTraversable.id_traverse

namespace Traversable

variable {t : Type u → Type u}

variable [Traversable t] [IsLawfulTraversable t]

variable (F G : Type u → Type u)

variable [Applicative F] [LawfulApplicative F]

variable [Applicative G] [LawfulApplicative G]

variable {α β γ : Type u}

variable (g : α → F β)

variable (h : β → G γ)

variable (f : β → γ)

#print Traversable.PureTransformation /-
/-- The natural applicative transformation from the identity functor
to `F`, defined by `pure : Π {α}, α → F α`. -/
def PureTransformation : ApplicativeTransformation id F
    where
  app := @pure F _
  preserves_pure' α x := rfl
  preserves_seq' α β f x := by
    simp only [map_pure, seq_pure]
    rfl
#align traversable.pure_transformation Traversable.PureTransformation
-/

#print Traversable.pureTransformation_apply /-
@[simp]
theorem pureTransformation_apply {α} (x : id α) : PureTransformation F x = pure x :=
  rfl
#align traversable.pure_transformation_apply Traversable.pureTransformation_apply
-/

variable {F G} (x : t β)

/- warning: traversable.map_eq_traverse_id -> Traversable.map_eq_traverse_id is a dubious translation:
lean 3 declaration is
  forall {t : Type.{u1} -> Type.{u1}} [_inst_1 : Traversable.{u1} t] [_inst_2 : IsLawfulTraversable.{u1} t _inst_1] {β : Type.{u1}} {γ : Type.{u1}} (f : β -> γ), Eq.{succ u1} ((t β) -> (t γ)) (Functor.map.{u1, u1} (fun {β : Type.{u1}} => t β) (Traversable.toFunctor.{u1} (fun {β : Type.{u1}} => t β) _inst_1) β γ f) (Traversable.traverse.{u1} t _inst_1 (id.{succ (succ u1)} Type.{u1}) (Monad.toApplicative.{u1, u1} (id.{succ (succ u1)} Type.{u1}) id.monad.{u1}) β γ (Function.comp.{succ u1, succ u1, succ u1} β γ (id.{succ (succ u1)} Type.{u1} γ) (id.mk.{succ u1} γ) f))
but is expected to have type
  forall {t : Type.{u1} -> Type.{u1}} [_inst_1 : Traversable.{u1} t] [_inst_2 : IsLawfulTraversable.{u1} t _inst_1] {β : Type.{u1}} {γ : Type.{u1}} (f : β -> γ), Eq.{succ u1} ((t β) -> (t γ)) (Functor.map.{u1, u1} t (Traversable.toFunctor.{u1} t _inst_1) β γ f) (Traversable.traverse.{u1} t _inst_1 Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1}) β γ (Function.comp.{succ u1, succ u1, succ u1} β γ (Id.{u1} γ) (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) γ) f))
Case conversion may be inaccurate. Consider using '#align traversable.map_eq_traverse_id Traversable.map_eq_traverse_idₓ'. -/
theorem map_eq_traverse_id : map f = @traverse t _ _ _ _ _ (id.mk ∘ f) :=
  funext fun y => (traverse_eq_map_id f y).symm
#align traversable.map_eq_traverse_id Traversable.map_eq_traverse_id

#print Traversable.map_traverse /-
theorem map_traverse (x : t α) : map f <$> traverse g x = traverse (map f ∘ g) x :=
  by
  rw [@map_eq_traverse_id t _ _ _ _ f]
  refine' (comp_traverse (id.mk ∘ f) g x).symm.trans _
  congr ; apply comp.applicative_comp_id
#align traversable.map_traverse Traversable.map_traverse
-/

#print Traversable.traverse_map /-
theorem traverse_map (f : β → F γ) (g : α → β) (x : t α) :
    traverse f (g <$> x) = traverse (f ∘ g) x :=
  by
  rw [@map_eq_traverse_id t _ _ _ _ g]
  refine' (comp_traverse f (id.mk ∘ g) x).symm.trans _
  congr ; apply comp.applicative_id_comp
#align traversable.traverse_map Traversable.traverse_map
-/

#print Traversable.pure_traverse /-
theorem pure_traverse (x : t α) : traverse pure x = (pure x : F (t α)) := by
  have : traverse pure x = pure (traverse id.mk x) :=
      (naturality (pure_transformation F) id.mk x).symm <;>
    rwa [id_traverse] at this
#align traversable.pure_traverse Traversable.pure_traverse
-/

/- warning: traversable.id_sequence -> Traversable.id_sequence is a dubious translation:
lean 3 declaration is
  forall {t : Type.{u1} -> Type.{u1}} [_inst_1 : Traversable.{u1} t] [_inst_2 : IsLawfulTraversable.{u1} t _inst_1] {α : Type.{u1}} (x : t α), Eq.{succ u1} (id.{succ (succ u1)} Type.{u1} (t α)) (sequence.{u1} t α (id.{succ (succ u1)} Type.{u1}) (Monad.toApplicative.{u1, u1} (id.{succ (succ u1)} Type.{u1}) id.monad.{u1}) _inst_1 (Functor.map.{u1, u1} t (Traversable.toFunctor.{u1} t _inst_1) α (id.{succ (succ u1)} Type.{u1} α) (id.mk.{succ u1} α) x)) (id.mk.{succ u1} (t α) x)
but is expected to have type
  forall {t : Type.{u1} -> Type.{u1}} [_inst_1 : Traversable.{u1} t] [_inst_2 : IsLawfulTraversable.{u1} t _inst_1] {α : Type.{u1}} (x : t α), Eq.{succ u1} (Id.{u1} (t α)) (sequence.{u1} t α Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1}) _inst_1 (Functor.map.{u1, u1} t (Traversable.toFunctor.{u1} t _inst_1) α (Id.{u1} α) (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) α) x)) (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) (t α) x)
Case conversion may be inaccurate. Consider using '#align traversable.id_sequence Traversable.id_sequenceₓ'. -/
theorem id_sequence (x : t α) : sequence (id.mk <$> x) = id.mk x := by
  simp [sequence, traverse_map, id_traverse] <;> rfl
#align traversable.id_sequence Traversable.id_sequence

/- warning: traversable.comp_sequence -> Traversable.comp_sequence is a dubious translation:
lean 3 declaration is
  forall {t : Type.{u1} -> Type.{u1}} [_inst_1 : Traversable.{u1} t] [_inst_2 : IsLawfulTraversable.{u1} t _inst_1] {F : Type.{u1} -> Type.{u1}} {G : Type.{u1} -> Type.{u1}} [_inst_3 : Applicative.{u1, u1} F] [_inst_4 : LawfulApplicative.{u1, u1} F _inst_3] [_inst_5 : Applicative.{u1, u1} G] [_inst_6 : LawfulApplicative.{u1, u1} G _inst_5] {α : Type.{u1}} (x : t (F (G α))), Eq.{succ u1} (Functor.Comp.{u1, u1, u1} F G (t α)) (sequence.{u1} t α (Functor.Comp.{u1, u1, u1} F G) (Functor.Comp.applicative.{u1, u1, u1} F G _inst_3 _inst_5) _inst_1 (Functor.map.{u1, u1} t (Traversable.toFunctor.{u1} t _inst_1) (F (G α)) (Functor.Comp.{u1, u1, u1} F G α) (Functor.Comp.mk.{u1, u1, u1} F G α) x)) (Functor.Comp.mk.{u1, u1, u1} F G (t α) (Functor.map.{u1, u1} F (Applicative.toFunctor.{u1, u1} F _inst_3) (t (G α)) (G (t α)) (sequence.{u1} t α G _inst_5 _inst_1) (sequence.{u1} t (G α) F _inst_3 _inst_1 x)))
but is expected to have type
  forall {t : Type.{u1} -> Type.{u1}} [_inst_1 : Traversable.{u1} t] [_inst_2 : IsLawfulTraversable.{u1} t _inst_1] {F : Type.{u1} -> Type.{u1}} {G : Type.{u1} -> Type.{u1}} [_inst_3 : Applicative.{u1, u1} F] [_inst_4 : LawfulApplicative.{u1, u1} F _inst_3] [_inst_5 : Applicative.{u1, u1} G] [_inst_6 : LawfulApplicative.{u1, u1} G _inst_5] {α : Type.{u1}} (x : t (F (G α))), Eq.{succ u1} (Functor.Comp.{u1, u1, u1} F G (t α)) (sequence.{u1} t α (Functor.Comp.{u1, u1, u1} F G) (Functor.Comp.instApplicativeComp.{u1, u1, u1} F G _inst_3 _inst_5) _inst_1 (Functor.map.{u1, u1} t (Traversable.toFunctor.{u1} t _inst_1) (F (G α)) (Functor.Comp.{u1, u1, u1} F G α) (Functor.Comp.mk.{u1, u1, u1} F G α) x)) (Functor.Comp.mk.{u1, u1, u1} F G (t α) (Functor.map.{u1, u1} F (Applicative.toFunctor.{u1, u1} F _inst_3) (t (G α)) (G (t α)) (sequence.{u1} t α G _inst_5 _inst_1) (sequence.{u1} t (G α) F _inst_3 _inst_1 x)))
Case conversion may be inaccurate. Consider using '#align traversable.comp_sequence Traversable.comp_sequenceₓ'. -/
theorem comp_sequence (x : t (F (G α))) :
    sequence (comp.mk <$> x) = Comp.mk (sequence <$> sequence x) := by
  simp [sequence, traverse_map] <;> rw [← comp_traverse] <;> simp [map_id]
#align traversable.comp_sequence Traversable.comp_sequence

#print Traversable.naturality' /-
theorem naturality' (η : ApplicativeTransformation F G) (x : t (F α)) :
    η (sequence x) = sequence (@η _ <$> x) := by simp [sequence, naturality, traverse_map]
#align traversable.naturality' Traversable.naturality'
-/

/- warning: traversable.traverse_id -> Traversable.traverse_id is a dubious translation:
lean 3 declaration is
  forall {t : Type.{u1} -> Type.{u1}} [_inst_1 : Traversable.{u1} t] [_inst_2 : IsLawfulTraversable.{u1} t _inst_1] {α : Type.{u1}}, Eq.{succ u1} ((t α) -> (id.{succ (succ u1)} Type.{u1} (t α))) (Traversable.traverse.{u1} t _inst_1 (id.{succ (succ u1)} Type.{u1}) (Monad.toApplicative.{u1, u1} (id.{succ (succ u1)} Type.{u1}) id.monad.{u1}) α α (id.mk.{succ u1} α)) (id.mk.{succ u1} (t α))
but is expected to have type
  forall {t : Type.{u1} -> Type.{u1}} [_inst_1 : Traversable.{u1} t] [_inst_2 : IsLawfulTraversable.{u1} t _inst_1] {α : Type.{u1}}, Eq.{succ u1} ((t α) -> (Id.{u1} (t α))) (Traversable.traverse.{u1} t _inst_1 Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1}) α α (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) α)) (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) (t α))
Case conversion may be inaccurate. Consider using '#align traversable.traverse_id Traversable.traverse_idₓ'. -/
@[functor_norm]
theorem traverse_id : traverse id.mk = (id.mk : t α → id (t α)) :=
  by
  ext
  exact id_traverse _
#align traversable.traverse_id Traversable.traverse_id

/- warning: traversable.traverse_comp -> Traversable.traverse_comp is a dubious translation:
lean 3 declaration is
  forall {t : Type.{u1} -> Type.{u1}} [_inst_1 : Traversable.{u1} t] [_inst_2 : IsLawfulTraversable.{u1} t _inst_1] {F : Type.{u1} -> Type.{u1}} {G : Type.{u1} -> Type.{u1}} [_inst_3 : Applicative.{u1, u1} F] [_inst_4 : LawfulApplicative.{u1, u1} F _inst_3] [_inst_5 : Applicative.{u1, u1} G] [_inst_6 : LawfulApplicative.{u1, u1} G _inst_5] {α : Type.{u1}} {β : Type.{u1}} {γ : Type.{u1}} (g : α -> (F β)) (h : β -> (G γ)), Eq.{succ u1} ((t α) -> (Functor.Comp.{u1, u1, u1} (fun {β : Type.{u1}} => F β) G (t γ))) (Traversable.traverse.{u1} (fun {α : Type.{u1}} => t α) _inst_1 (Functor.Comp.{u1, u1, u1} (fun {β : Type.{u1}} => F β) G) (Functor.Comp.applicative.{u1, u1, u1} (fun {β : Type.{u1}} => F β) G _inst_3 _inst_5) α γ (Function.comp.{succ u1, succ u1, succ u1} α (F (G γ)) (Functor.Comp.{u1, u1, u1} (fun {β : Type.{u1}} => F β) G γ) (Functor.Comp.mk.{u1, u1, u1} (fun {β : Type.{u1}} => F β) G γ) (Function.comp.{succ u1, succ u1, succ u1} α (F β) (F (G γ)) (Functor.map.{u1, u1} (fun {β : Type.{u1}} => F β) (Applicative.toFunctor.{u1, u1} (fun {β : Type.{u1}} => F β) _inst_3) β (G γ) h) g))) (Function.comp.{succ u1, succ u1, succ u1} (t α) (F (G (t γ))) (Functor.Comp.{u1, u1, u1} F G (t γ)) (Functor.Comp.mk.{u1, u1, u1} F G (t γ)) (Function.comp.{succ u1, succ u1, succ u1} (t α) (F (t β)) (F (G (t γ))) (Functor.map.{u1, u1} F (Applicative.toFunctor.{u1, u1} F _inst_3) (t β) (G (t γ)) (Traversable.traverse.{u1} t _inst_1 G _inst_5 β γ h)) (Traversable.traverse.{u1} t _inst_1 F _inst_3 α β g)))
but is expected to have type
  forall {t : Type.{u1} -> Type.{u1}} [_inst_1 : Traversable.{u1} t] [_inst_2 : IsLawfulTraversable.{u1} t _inst_1] {F : Type.{u1} -> Type.{u1}} {G : Type.{u1} -> Type.{u1}} [_inst_3 : Applicative.{u1, u1} F] [_inst_4 : LawfulApplicative.{u1, u1} F _inst_3] [_inst_5 : Applicative.{u1, u1} G] [_inst_6 : LawfulApplicative.{u1, u1} G _inst_5] {α : Type.{u1}} {β : Type.{u1}} {γ : Type.{u1}} (g : α -> (F β)) (h : β -> (G γ)), Eq.{succ u1} ((t α) -> (Functor.Comp.{u1, u1, u1} F G (t γ))) (Traversable.traverse.{u1} t _inst_1 (Functor.Comp.{u1, u1, u1} F G) (Functor.Comp.instApplicativeComp.{u1, u1, u1} F G _inst_3 _inst_5) α γ (Function.comp.{succ u1, succ u1, succ u1} α (F (G γ)) (Functor.Comp.{u1, u1, u1} F G γ) (Functor.Comp.mk.{u1, u1, u1} F G γ) (Function.comp.{succ u1, succ u1, succ u1} α (F β) (F (G γ)) (Functor.map.{u1, u1} F (Applicative.toFunctor.{u1, u1} F _inst_3) β (G γ) h) g))) (Function.comp.{succ u1, succ u1, succ u1} (t α) (F (G (t γ))) (Functor.Comp.{u1, u1, u1} F G (t γ)) (Functor.Comp.mk.{u1, u1, u1} F G (t γ)) (Function.comp.{succ u1, succ u1, succ u1} (t α) (F (t β)) (F (G (t γ))) (Functor.map.{u1, u1} F (Applicative.toFunctor.{u1, u1} F _inst_3) (t β) (G (t γ)) (Traversable.traverse.{u1} t _inst_1 G _inst_5 β γ h)) (Traversable.traverse.{u1} t _inst_1 F _inst_3 α β g)))
Case conversion may be inaccurate. Consider using '#align traversable.traverse_comp Traversable.traverse_compₓ'. -/
@[functor_norm]
theorem traverse_comp (g : α → F β) (h : β → G γ) :
    traverse (comp.mk ∘ map h ∘ g) =
      (comp.mk ∘ map (traverse h) ∘ traverse g : t α → Comp F G (t γ)) :=
  by
  ext
  exact comp_traverse _ _ _
#align traversable.traverse_comp Traversable.traverse_comp

/- warning: traversable.traverse_eq_map_id' -> Traversable.traverse_eq_map_id' is a dubious translation:
lean 3 declaration is
  forall {t : Type.{u1} -> Type.{u1}} [_inst_1 : Traversable.{u1} t] [_inst_2 : IsLawfulTraversable.{u1} t _inst_1] {β : Type.{u1}} {γ : Type.{u1}} (f : β -> γ), Eq.{succ u1} ((t β) -> (id.{succ (succ u1)} Type.{u1} (t γ))) (Traversable.traverse.{u1} (fun {β : Type.{u1}} => t β) _inst_1 (id.{succ (succ u1)} Type.{u1}) (Monad.toApplicative.{u1, u1} (id.{succ (succ u1)} Type.{u1}) id.monad.{u1}) β γ (Function.comp.{succ u1, succ u1, succ u1} β γ (id.{succ (succ u1)} Type.{u1} γ) (id.mk.{succ u1} γ) f)) (Function.comp.{succ u1, succ u1, succ u1} (t β) (t γ) (id.{succ (succ u1)} Type.{u1} (t γ)) (id.mk.{succ u1} (t γ)) (Functor.map.{u1, u1} t (Traversable.toFunctor.{u1} t _inst_1) β γ f))
but is expected to have type
  forall {t : Type.{u1} -> Type.{u1}} [_inst_1 : Traversable.{u1} t] [_inst_2 : IsLawfulTraversable.{u1} t _inst_1] {β : Type.{u1}} {γ : Type.{u1}} (f : β -> γ), Eq.{succ u1} ((t β) -> (Id.{u1} (t γ))) (Traversable.traverse.{u1} t _inst_1 Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1}) β γ (Function.comp.{succ u1, succ u1, succ u1} β γ (Id.{u1} γ) (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) γ) f)) (Function.comp.{succ u1, succ u1, succ u1} (t β) (t γ) (Id.{u1} (t γ)) (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) (t γ)) (Functor.map.{u1, u1} t (Traversable.toFunctor.{u1} t _inst_1) β γ f))
Case conversion may be inaccurate. Consider using '#align traversable.traverse_eq_map_id' Traversable.traverse_eq_map_id'ₓ'. -/
theorem traverse_eq_map_id' (f : β → γ) : traverse (id.mk ∘ f) = id.mk ∘ (map f : t β → t γ) :=
  by
  ext
  exact traverse_eq_map_id _ _
#align traversable.traverse_eq_map_id' Traversable.traverse_eq_map_id'

#print Traversable.traverse_map' /-
-- @[functor_norm]
theorem traverse_map' (g : α → β) (h : β → G γ) :
    traverse (h ∘ g) = (traverse h ∘ map g : t α → G (t γ)) :=
  by
  ext
  rw [comp_app, traverse_map]
#align traversable.traverse_map' Traversable.traverse_map'
-/

#print Traversable.map_traverse' /-
theorem map_traverse' (g : α → G β) (h : β → γ) :
    traverse (map h ∘ g) = (map (map h) ∘ traverse g : t α → G (t γ)) :=
  by
  ext
  rw [comp_app, map_traverse]
#align traversable.map_traverse' Traversable.map_traverse'
-/

#print Traversable.naturality_pf /-
theorem naturality_pf (η : ApplicativeTransformation F G) (f : α → F β) :
    traverse (@η _ ∘ f) = @η _ ∘ (traverse f : t α → F (t β)) :=
  by
  ext
  rw [comp_app, naturality]
#align traversable.naturality_pf Traversable.naturality_pf
-/

end Traversable

