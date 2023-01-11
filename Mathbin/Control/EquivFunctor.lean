/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module control.equiv_functor
! leanprover-community/mathlib commit ccad6d5093bd2f5c6ca621fc74674cce51355af6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Equiv.Defs

/-!
# Functions functorial with respect to equivalences

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

An `equiv_functor` is a function from `Type → Type` equipped with the additional data of
coherently mapping equivalences to equivalences.

In categorical language, it is an endofunctor of the "core" of the category `Type`.
-/


universe u₀ u₁ u₂ v₀ v₁ v₂

open Function

#print EquivFunctor /-
/-- An `equiv_functor` is only functorial with respect to equivalences.

To construct an `equiv_functor`, it suffices to supply just the function `f α → f β` from
an equivalence `α ≃ β`, and then prove the functor laws. It's then a consequence that
this function is part of an equivalence, provided by `equiv_functor.map_equiv`.
-/
class EquivFunctor (f : Type u₀ → Type u₁) where
  map : ∀ {α β}, α ≃ β → f α → f β
  map_refl' : ∀ α, map (Equiv.refl α) = @id (f α) := by obviously
  map_trans' : ∀ {α β γ} (k : α ≃ β) (h : β ≃ γ), map (k.trans h) = map h ∘ map k := by obviously
#align equiv_functor EquivFunctor
-/

restate_axiom EquivFunctor.map_refl'

restate_axiom EquivFunctor.map_trans'

attribute [simp] EquivFunctor.map_refl

namespace EquivFunctor

section

variable (f : Type u₀ → Type u₁) [EquivFunctor f] {α β : Type u₀} (e : α ≃ β)

#print EquivFunctor.mapEquiv /-
/-- An `equiv_functor` in fact takes every equiv to an equiv. -/
def mapEquiv : f α ≃ f β where
  toFun := EquivFunctor.map e
  invFun := EquivFunctor.map e.symm
  left_inv x := by
    convert (congr_fun (EquivFunctor.map_trans e e.symm) x).symm
    simp
  right_inv y := by
    convert (congr_fun (EquivFunctor.map_trans e.symm e) y).symm
    simp
#align equiv_functor.map_equiv EquivFunctor.mapEquiv
-/

#print EquivFunctor.mapEquiv_apply /-
@[simp]
theorem mapEquiv_apply (x : f α) : mapEquiv f e x = EquivFunctor.map e x :=
  rfl
#align equiv_functor.map_equiv_apply EquivFunctor.mapEquiv_apply
-/

#print EquivFunctor.mapEquiv_symm_apply /-
theorem mapEquiv_symm_apply (y : f β) : (mapEquiv f e).symm y = EquivFunctor.map e.symm y :=
  rfl
#align equiv_functor.map_equiv_symm_apply EquivFunctor.mapEquiv_symm_apply
-/

#print EquivFunctor.mapEquiv_refl /-
@[simp]
theorem mapEquiv_refl (α) : mapEquiv f (Equiv.refl α) = Equiv.refl (f α) := by
  simpa [EquivFunctor.mapEquiv]
#align equiv_functor.map_equiv_refl EquivFunctor.mapEquiv_refl
-/

#print EquivFunctor.mapEquiv_symm /-
@[simp]
theorem mapEquiv_symm : (mapEquiv f e).symm = mapEquiv f e.symm :=
  Equiv.ext <| mapEquiv_symm_apply f e
#align equiv_functor.map_equiv_symm EquivFunctor.mapEquiv_symm
-/

#print EquivFunctor.mapEquiv_trans /-
/-- The composition of `map_equiv`s is carried over the `equiv_functor`.
For plain `functor`s, this lemma is named `map_map` when applied
or `map_comp_map` when not applied.
-/
@[simp]
theorem mapEquiv_trans {γ : Type u₀} (ab : α ≃ β) (bc : β ≃ γ) :
    (mapEquiv f ab).trans (mapEquiv f bc) = mapEquiv f (ab.trans bc) :=
  Equiv.ext fun x => by simp [map_equiv, map_trans']
#align equiv_functor.map_equiv_trans EquivFunctor.mapEquiv_trans
-/

end

#print EquivFunctor.ofLawfulFunctor /-
instance (priority := 100) ofLawfulFunctor (f : Type u₀ → Type u₁) [Functor f] [LawfulFunctor f] :
    EquivFunctor f where
  map α β e := Functor.map e
  map_refl' α := by
    ext
    apply LawfulFunctor.id_map
  map_trans' α β γ k h := by
    ext x
    apply LawfulFunctor.comp_map k h x
#align equiv_functor.of_is_lawful_functor EquivFunctor.ofLawfulFunctor
-/

#print EquivFunctor.mapEquiv.injective /-
theorem mapEquiv.injective (f : Type u₀ → Type u₁) [Applicative f] [LawfulApplicative f]
    {α β : Type u₀} (h : ∀ γ, Function.Injective (pure : γ → f γ)) :
    Function.Injective (@EquivFunctor.mapEquiv f _ α β) := fun e₁ e₂ H =>
  Equiv.ext fun x => h β (by simpa [EquivFunctor.map] using Equiv.congr_fun H (pure x))
#align equiv_functor.map_equiv.injective EquivFunctor.mapEquiv.injective
-/

end EquivFunctor

