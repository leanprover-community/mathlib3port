/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.functor.reflects_isomorphisms
! leanprover-community/mathlib commit e001509c11c4d0f549d91d89da95b4a0b43c714f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Balanced
import Mathbin.CategoryTheory.Functor.EpiMono
import Mathbin.CategoryTheory.Functor.FullyFaithful

/-!
# Functors which reflect isomorphisms

A functor `F` reflects isomorphisms if whenever `F.map f` is an isomorphism, `f` was too.

It is formalized as a `Prop` valued typeclass `reflects_isomorphisms F`.

Any fully faithful functor reflects isomorphisms.
-/


open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]

section ReflectsIso

variable {D : Type u₂} [Category.{v₂} D]

variable {E : Type u₃} [Category.{v₃} E]

/-- Define what it means for a functor `F : C ⥤ D` to reflect isomorphisms: for any
morphism `f : A ⟶ B`, if `F.map f` is an isomorphism then `f` is as well.
Note that we do not assume or require that `F` is faithful.
-/
class ReflectsIsomorphisms (F : C ⥤ D) : Prop where
  reflects : ∀ {A B : C} (f : A ⟶ B) [IsIso (F.map f)], IsIso f
#align category_theory.reflects_isomorphisms CategoryTheory.ReflectsIsomorphisms

/-- If `F` reflects isos and `F.map f` is an iso, then `f` is an iso. -/
theorem is_iso_of_reflects_iso {A B : C} (f : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)]
    [ReflectsIsomorphisms F] : IsIso f :=
  ReflectsIsomorphisms.reflects F f
#align category_theory.is_iso_of_reflects_iso CategoryTheory.is_iso_of_reflects_iso

instance (priority := 100) of_full_and_faithful (F : C ⥤ D) [Full F] [Faithful F] :
    ReflectsIsomorphisms F
    where reflects X Y f i :=
    ⟨⟨F.preimage (inv (F.map f)), ⟨F.map_injective (by simp), F.map_injective (by simp)⟩⟩⟩
#align category_theory.of_full_and_faithful CategoryTheory.of_full_and_faithful

instance (F : C ⥤ D) (G : D ⥤ E) [ReflectsIsomorphisms F] [ReflectsIsomorphisms G] :
    ReflectsIsomorphisms (F ⋙ G) :=
  ⟨fun _ _ f (hf : IsIso (G.map _)) => by
    skip
    haveI := is_iso_of_reflects_iso (F.map f) G
    exact is_iso_of_reflects_iso f F⟩

instance (priority := 100) reflects_isomorphisms_of_reflects_monomorphisms_of_reflects_epimorphisms
    [Balanced C] (F : C ⥤ D) [ReflectsMonomorphisms F] [ReflectsEpimorphisms F] :
    ReflectsIsomorphisms F
    where reflects A B f hf := by
    skip
    haveI : epi f := epi_of_epi_map F inferInstance
    haveI : mono f := mono_of_mono_map F inferInstance
    exact is_iso_of_mono_of_epi f
#align
  category_theory.reflects_isomorphisms_of_reflects_monomorphisms_of_reflects_epimorphisms CategoryTheory.reflects_isomorphisms_of_reflects_monomorphisms_of_reflects_epimorphisms

end ReflectsIso

end CategoryTheory

