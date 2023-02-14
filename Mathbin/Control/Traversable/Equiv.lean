/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module control.traversable.equiv
! leanprover-community/mathlib commit 48085f140e684306f9e7da907cd5932056d1aded
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Control.Traversable.Lemmas
import Mathbin.Logic.Equiv.Defs

/-!
# Transferring `traversable` instances along isomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file allows to transfer `traversable` instances along isomorphisms.

## Main declarations

* `equiv.map`: Turns functorially a function `α → β` into a function `t' α → t' β` using the functor
  `t` and the equivalence `Π α, t α ≃ t' α`.
* `equiv.functor`: `equiv.map` as a functor.
* `equiv.traverse`: Turns traversably a function `α → m β` into a function `t' α → m (t' β)` using
  the traversable functor `t` and the equivalence `Π α, t α ≃ t' α`.
* `equiv.traversable`: `equiv.traverse` as a traversable functor.
* `equiv.is_lawful_traversable`: `equiv.traverse` as a lawful traversable functor.
-/


universe u

namespace Equiv

section Functor

parameter {t t' : Type u → Type u}

parameter (eqv : ∀ α, t α ≃ t' α)

variable [Functor t]

open Functor

#print Equiv.map /-
/-- Given a functor `t`, a function `t' : Type u → Type u`, and
equivalences `t α ≃ t' α` for all `α`, then every function `α → β` can
be mapped to a function `t' α → t' β` functorially (see
`equiv.functor`). -/
protected def map {α β : Type u} (f : α → β) (x : t' α) : t' β :=
  eqv β <| map f ((eqv α).symm x)
#align equiv.map Equiv.map
-/

#print Equiv.functor /-
/-- The function `equiv.map` transfers the functoriality of `t` to
`t'` using the equivalences `eqv`.  -/
protected def functor : Functor t' where map := @Equiv.map _
#align equiv.functor Equiv.functor
-/

variable [LawfulFunctor t]

#print Equiv.id_map /-
protected theorem id_map {α : Type u} (x : t' α) : Equiv.map id x = x := by simp [Equiv.map, id_map]
#align equiv.id_map Equiv.id_map
-/

#print Equiv.comp_map /-
protected theorem comp_map {α β γ : Type u} (g : α → β) (h : β → γ) (x : t' α) :
    Equiv.map (h ∘ g) x = Equiv.map h (Equiv.map g x) := by simp [Equiv.map] <;> apply comp_map
#align equiv.comp_map Equiv.comp_map
-/

#print Equiv.lawfulFunctor /-
protected theorem lawfulFunctor : @LawfulFunctor _ Equiv.functor :=
  { id_map := @Equiv.id_map _ _
    comp_map := @Equiv.comp_map _ _ }
#align equiv.is_lawful_functor Equiv.lawfulFunctor
-/

#print Equiv.lawfulFunctor' /-
protected theorem lawfulFunctor' [F : Functor t']
    (h₀ : ∀ {α β} (f : α → β), Functor.map f = Equiv.map f)
    (h₁ : ∀ {α β} (f : β), Functor.mapConst f = (Equiv.map ∘ Function.const α) f) :
    LawfulFunctor t' :=
  by
  have : F = Equiv.functor := by
    cases F
    dsimp [Equiv.functor]
    congr <;> ext <;> [rw [← h₀], rw [← h₁]]
  subst this
  exact Equiv.lawfulFunctor
#align equiv.is_lawful_functor' Equiv.lawfulFunctor'
-/

end Functor

section Traversable

parameter {t t' : Type u → Type u}

parameter (eqv : ∀ α, t α ≃ t' α)

variable [Traversable t]

variable {m : Type u → Type u} [Applicative m]

variable {α β : Type u}

#print Equiv.traverse /-
/-- Like `equiv.map`, a function `t' : Type u → Type u` can be given
the structure of a traversable functor using a traversable functor
`t'` and equivalences `t α ≃ t' α` for all α.  See `equiv.traversable`. -/
protected def traverse (f : α → m β) (x : t' α) : m (t' β) :=
  eqv β <$> traverse f ((eqv α).symm x)
#align equiv.traverse Equiv.traverse
-/

#print Equiv.traversable /-
/-- The function `equiv.traverse` transfers a traversable functor
instance across the equivalences `eqv`. -/
protected def traversable : Traversable t'
    where
  toFunctor := Equiv.functor eqv
  traverse := @Equiv.traverse _
#align equiv.traversable Equiv.traversable
-/

end Traversable

section Equiv

parameter {t t' : Type u → Type u}

parameter (eqv : ∀ α, t α ≃ t' α)

variable [Traversable t] [IsLawfulTraversable t]

variable {F G : Type u → Type u} [Applicative F] [Applicative G]

variable [LawfulApplicative F] [LawfulApplicative G]

variable (η : ApplicativeTransformation F G)

variable {α β γ : Type u}

open IsLawfulTraversable Functor

/- warning: equiv.id_traverse -> Equiv.id_traverse is a dubious translation:
lean 3 declaration is
  forall {t : Type.{u1} -> Type.{u1}} {t' : Type.{u1} -> Type.{u1}} (eqv : forall (α : Type.{u1}), Equiv.{succ u1, succ u1} (t α) (t' α)) [_inst_1 : Traversable.{u1} t] [_inst_2 : IsLawfulTraversable.{u1} t _inst_1] {α : Type.{u1}} (x : t' α), Eq.{succ u1} (id.{succ (succ u1)} Type.{u1} (t' α)) (Equiv.traverse.{u1} (fun (α : Type.{u1}) => t α) (fun (α : Type.{u1}) => t' α) eqv _inst_1 (id.{succ (succ u1)} Type.{u1}) (Monad.toApplicative.{u1, u1} (id.{succ (succ u1)} Type.{u1}) id.monad.{u1}) α α (id.mk.{succ u1} α) x) x
but is expected to have type
  forall {t : Type.{u1} -> Type.{u1}} {t' : Type.{u1} -> Type.{u1}} (eqv : forall (α : Type.{u1}), Equiv.{succ u1, succ u1} (t α) (t' α)) [_inst_1 : Traversable.{u1} t] [_inst_2 : IsLawfulTraversable.{u1} t _inst_1] {α : Type.{u1}} (x : t' α), Eq.{succ u1} (Id.{u1} (t' α)) (Equiv.traverse.{u1} (fun (α : Type.{u1}) => t α) (fun (α : Type.{u1}) => t' α) eqv _inst_1 Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1}) α α (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) α) x) x
Case conversion may be inaccurate. Consider using '#align equiv.id_traverse Equiv.id_traverseₓ'. -/
protected theorem id_traverse (x : t' α) : Equiv.traverse eqv id.mk x = x := by
  simp! [Equiv.traverse, idBind, id_traverse, Functor.map, functor_norm]
#align equiv.id_traverse Equiv.id_traverse

/- warning: equiv.traverse_eq_map_id -> Equiv.traverse_eq_map_id is a dubious translation:
lean 3 declaration is
  forall {t : Type.{u1} -> Type.{u1}} {t' : Type.{u1} -> Type.{u1}} (eqv : forall (α : Type.{u1}), Equiv.{succ u1, succ u1} (t α) (t' α)) [_inst_1 : Traversable.{u1} t] [_inst_2 : IsLawfulTraversable.{u1} t _inst_1] {α : Type.{u1}} {β : Type.{u1}} (f : α -> β) (x : t' α), Eq.{succ u1} (id.{succ (succ u1)} Type.{u1} (t' β)) (Equiv.traverse.{u1} (fun (α : Type.{u1}) => t α) (fun (α : Type.{u1}) => t' α) eqv _inst_1 (id.{succ (succ u1)} Type.{u1}) (Monad.toApplicative.{u1, u1} (id.{succ (succ u1)} Type.{u1}) id.monad.{u1}) α β (Function.comp.{succ u1, succ u1, succ u1} α β (id.{succ (succ u1)} Type.{u1} β) (id.mk.{succ u1} β) f) x) (id.mk.{succ u1} (t' β) (Equiv.map.{u1} (fun (α : Type.{u1}) => t α) t' eqv (Traversable.toFunctor.{u1} (fun (α : Type.{u1}) => t α) _inst_1) α β f x))
but is expected to have type
  forall {t : Type.{u1} -> Type.{u1}} {t' : Type.{u1} -> Type.{u1}} (eqv : forall (α : Type.{u1}), Equiv.{succ u1, succ u1} (t α) (t' α)) [_inst_1 : Traversable.{u1} t] [_inst_2 : IsLawfulTraversable.{u1} t _inst_1] {α : Type.{u1}} {β : Type.{u1}} (f : α -> β) (x : t' α), Eq.{succ u1} (Id.{u1} (t' β)) (Equiv.traverse.{u1} (fun (α : Type.{u1}) => t α) (fun (α : Type.{u1}) => t' α) eqv _inst_1 Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1}) α β (Function.comp.{succ u1, succ u1, succ u1} α β (Id.{u1} β) (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) β) f) x) (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) (t' β) (Equiv.map.{u1} (fun (α : Type.{u1}) => t α) (fun (α : Type.{u1}) => t' α) eqv (Traversable.toFunctor.{u1} (fun (α : Type.{u1}) => t α) _inst_1) α β f x))
Case conversion may be inaccurate. Consider using '#align equiv.traverse_eq_map_id Equiv.traverse_eq_map_idₓ'. -/
protected theorem traverse_eq_map_id (f : α → β) (x : t' α) :
    Equiv.traverse eqv (id.mk ∘ f) x = id.mk (Equiv.map eqv f x) := by
  simp [Equiv.traverse, traverse_eq_map_id, functor_norm] <;> rfl
#align equiv.traverse_eq_map_id Equiv.traverse_eq_map_id

/- warning: equiv.comp_traverse -> Equiv.comp_traverse is a dubious translation:
lean 3 declaration is
  forall {t : Type.{u1} -> Type.{u1}} {t' : Type.{u1} -> Type.{u1}} (eqv : forall (α : Type.{u1}), Equiv.{succ u1, succ u1} (t α) (t' α)) [_inst_1 : Traversable.{u1} t] [_inst_2 : IsLawfulTraversable.{u1} t _inst_1] {F : Type.{u1} -> Type.{u1}} {G : Type.{u1} -> Type.{u1}} [_inst_3 : Applicative.{u1, u1} F] [_inst_4 : Applicative.{u1, u1} G] [_inst_5 : LawfulApplicative.{u1, u1} F _inst_3] [_inst_6 : LawfulApplicative.{u1, u1} G _inst_4] {α : Type.{u1}} {β : Type.{u1}} {γ : Type.{u1}} (f : β -> (F γ)) (g : α -> (G β)) (x : t' α), Eq.{succ u1} (Functor.Comp.{u1, u1, u1} (fun {β : Type.{u1}} => G β) F (t' γ)) (Equiv.traverse.{u1} (fun (α : Type.{u1}) => t α) (fun (α : Type.{u1}) => t' α) eqv _inst_1 (Functor.Comp.{u1, u1, u1} (fun {β : Type.{u1}} => G β) F) (Functor.Comp.applicative.{u1, u1, u1} (fun {β : Type.{u1}} => G β) F _inst_4 _inst_3) α γ (Function.comp.{succ u1, succ u1, succ u1} α (G (F γ)) (Functor.Comp.{u1, u1, u1} (fun {β : Type.{u1}} => G β) F γ) (Functor.Comp.mk.{u1, u1, u1} (fun {β : Type.{u1}} => G β) F γ) (Function.comp.{succ u1, succ u1, succ u1} α (G β) (G (F γ)) (Functor.map.{u1, u1} (fun {β : Type.{u1}} => G β) (Applicative.toFunctor.{u1, u1} (fun {β : Type.{u1}} => G β) _inst_4) β (F γ) f) g)) x) (Functor.Comp.mk.{u1, u1, u1} (fun {β : Type.{u1}} => G β) F (t' γ) (Functor.map.{u1, u1} G (Applicative.toFunctor.{u1, u1} G _inst_4) (t' β) (F (t' γ)) (Equiv.traverse.{u1} (fun (α : Type.{u1}) => t α) t' eqv _inst_1 F _inst_3 β γ f) (Equiv.traverse.{u1} (fun (α : Type.{u1}) => t α) t' eqv _inst_1 G _inst_4 α β g x)))
but is expected to have type
  forall {t : Type.{u1} -> Type.{u1}} {t' : Type.{u1} -> Type.{u1}} (eqv : forall (α : Type.{u1}), Equiv.{succ u1, succ u1} (t α) (t' α)) [_inst_1 : Traversable.{u1} t] [_inst_2 : IsLawfulTraversable.{u1} t _inst_1] {F : Type.{u1} -> Type.{u1}} {G : Type.{u1} -> Type.{u1}} [_inst_3 : Applicative.{u1, u1} F] [_inst_4 : Applicative.{u1, u1} G] [_inst_5 : LawfulApplicative.{u1, u1} F _inst_3] [_inst_6 : LawfulApplicative.{u1, u1} G _inst_4] {α : Type.{u1}} {β : Type.{u1}} {γ : Type.{u1}} (f : β -> (F γ)) (g : α -> (G β)) (x : t' α), Eq.{succ u1} (Functor.Comp.{u1, u1, u1} G F (t' γ)) (Equiv.traverse.{u1} (fun (α : Type.{u1}) => t α) (fun (α : Type.{u1}) => t' α) eqv _inst_1 (Functor.Comp.{u1, u1, u1} G F) (Functor.Comp.instApplicativeComp.{u1, u1, u1} G F _inst_4 _inst_3) α γ (Function.comp.{succ u1, succ u1, succ u1} α (G (F γ)) (Functor.Comp.{u1, u1, u1} G F γ) (Functor.Comp.mk.{u1, u1, u1} G F γ) (Function.comp.{succ u1, succ u1, succ u1} α (G β) (G (F γ)) (Functor.map.{u1, u1} G (Applicative.toFunctor.{u1, u1} G _inst_4) β (F γ) f) g)) x) (Functor.Comp.mk.{u1, u1, u1} G F (t' γ) (Functor.map.{u1, u1} G (Applicative.toFunctor.{u1, u1} G _inst_4) (t' β) (F (t' γ)) (Equiv.traverse.{u1} (fun (α : Type.{u1}) => t α) (fun (α : Type.{u1}) => t' α) eqv _inst_1 F _inst_3 β γ f) (Equiv.traverse.{u1} (fun (α : Type.{u1}) => t α) (fun (α : Type.{u1}) => t' α) eqv _inst_1 G _inst_4 α β g x)))
Case conversion may be inaccurate. Consider using '#align equiv.comp_traverse Equiv.comp_traverseₓ'. -/
protected theorem comp_traverse (f : β → F γ) (g : α → G β) (x : t' α) :
    Equiv.traverse eqv (Comp.mk ∘ Functor.map f ∘ g) x =
      Comp.mk (Equiv.traverse eqv f <$> Equiv.traverse eqv g x) :=
  by simp [Equiv.traverse, comp_traverse, functor_norm] <;> congr <;> ext <;> simp
#align equiv.comp_traverse Equiv.comp_traverse

#print Equiv.naturality /-
protected theorem naturality (f : α → F β) (x : t' α) :
    η (Equiv.traverse eqv f x) = Equiv.traverse eqv (@η _ ∘ f) x := by
  simp only [Equiv.traverse, functor_norm]
#align equiv.naturality Equiv.naturality
-/

#print Equiv.isLawfulTraversable /-
/-- The fact that `t` is a lawful traversable functor carries over the
equivalences to `t'`, with the traversable functor structure given by
`equiv.traversable`. -/
protected def isLawfulTraversable : @IsLawfulTraversable t' (Equiv.traversable eqv)
    where
  to_lawfulFunctor := @Equiv.lawfulFunctor _ _ eqv _ _
  id_traverse := @Equiv.id_traverse _ _
  comp_traverse := @Equiv.comp_traverse _ _
  traverse_eq_map_id := @Equiv.traverse_eq_map_id _ _
  naturality := @Equiv.naturality _ _
#align equiv.is_lawful_traversable Equiv.isLawfulTraversable
-/

#print Equiv.isLawfulTraversable' /-
/-- If the `traversable t'` instance has the properties that `map`,
`map_const`, and `traverse` are equal to the ones that come from
carrying the traversable functor structure from `t` over the
equivalences, then the fact that `t` is a lawful traversable functor
carries over as well. -/
protected def isLawfulTraversable' [_i : Traversable t']
    (h₀ : ∀ {α β} (f : α → β), map f = Equiv.map eqv f)
    (h₁ : ∀ {α β} (f : β), mapConst f = (Equiv.map eqv ∘ Function.const α) f)
    (h₂ :
      ∀ {F : Type u → Type u} [Applicative F],
        ∀ [LawfulApplicative F] {α β} (f : α → F β), traverse f = Equiv.traverse eqv f) :
    IsLawfulTraversable t' :=
  by
  -- we can't use the same approach as for `is_lawful_functor'` because
    -- h₂ needs a `is_lawful_applicative` assumption
    refine' { to_lawfulFunctor := Equiv.lawfulFunctor' eqv @h₀ @h₁.. } <;>
    intros
  · rw [h₂, Equiv.id_traverse]
    infer_instance
  · rw [h₂, Equiv.comp_traverse f g x, h₂]
    congr
    rw [h₂]
    all_goals infer_instance
  · rw [h₂, Equiv.traverse_eq_map_id, h₀] <;> infer_instance
  · rw [h₂, Equiv.naturality, h₂] <;> infer_instance
#align equiv.is_lawful_traversable' Equiv.isLawfulTraversable'
-/

end Equiv

end Equiv

