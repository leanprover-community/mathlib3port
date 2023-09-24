/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import CategoryTheory.Balanced
import CategoryTheory.Functor.EpiMono
import CategoryTheory.Functor.FullyFaithful

#align_import category_theory.functor.reflects_isomorphisms from "leanprover-community/mathlib"@"ef7acf407d265ad4081c8998687e994fa80ba70c"

/-!
# Functors which reflect isomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

#print CategoryTheory.ReflectsIsomorphisms /-
/-- Define what it means for a functor `F : C ⥤ D` to reflect isomorphisms: for any
morphism `f : A ⟶ B`, if `F.map f` is an isomorphism then `f` is as well.
Note that we do not assume or require that `F` is faithful.
-/
class ReflectsIsomorphisms (F : C ⥤ D) : Prop where
  reflects : ∀ {A B : C} (f : A ⟶ B) [IsIso (F.map f)], IsIso f
#align category_theory.reflects_isomorphisms CategoryTheory.ReflectsIsomorphisms
-/

#print CategoryTheory.isIso_of_reflects_iso /-
/-- If `F` reflects isos and `F.map f` is an iso, then `f` is an iso. -/
theorem isIso_of_reflects_iso {A B : C} (f : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)]
    [ReflectsIsomorphisms F] : IsIso f :=
  ReflectsIsomorphisms.reflects F f
#align category_theory.is_iso_of_reflects_iso CategoryTheory.isIso_of_reflects_iso
-/

#print CategoryTheory.reflectsIsomorphisms_of_full_and_faithful /-
instance (priority := 100) reflectsIsomorphisms_of_full_and_faithful (F : C ⥤ D) [Full F]
    [Faithful F] : ReflectsIsomorphisms F
    where reflects X Y f i :=
    ⟨⟨F.preimage (inv (F.map f)), ⟨F.map_injective (by simp), F.map_injective (by simp)⟩⟩⟩
#align category_theory.of_full_and_faithful CategoryTheory.reflectsIsomorphisms_of_full_and_faithful
-/

instance (F : C ⥤ D) (G : D ⥤ E) [ReflectsIsomorphisms F] [ReflectsIsomorphisms G] :
    ReflectsIsomorphisms (F ⋙ G) :=
  ⟨fun _ _ f (hf : IsIso (G.map _)) => by skip; haveI := is_iso_of_reflects_iso (F.map f) G;
    exact is_iso_of_reflects_iso f F⟩

#print CategoryTheory.reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms /-
instance (priority := 100) reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms
    [Balanced C] (F : C ⥤ D) [ReflectsMonomorphisms F] [ReflectsEpimorphisms F] :
    ReflectsIsomorphisms F
    where reflects A B f hf := by
    skip
    haveI : epi f := epi_of_epi_map F inferInstance
    haveI : mono f := mono_of_mono_map F inferInstance
    exact is_iso_of_mono_of_epi f
#align category_theory.reflects_isomorphisms_of_reflects_monomorphisms_of_reflects_epimorphisms CategoryTheory.reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms
-/

end ReflectsIso

end CategoryTheory

