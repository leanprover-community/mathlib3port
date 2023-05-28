/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module category_theory.functor.epi_mono
! leanprover-community/mathlib commit ef7acf407d265ad4081c8998687e994fa80ba70c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.EpiMono
import Mathbin.CategoryTheory.Limits.Shapes.StrongEpi
import Mathbin.CategoryTheory.LiftingProperties.Adjunction

/-!
# Preservation and reflection of monomorphisms and epimorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We provide typeclasses that state that a functor preserves or reflects monomorphisms or
epimorphisms.
-/


open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E]

#print CategoryTheory.Functor.PreservesMonomorphisms /-
/-- A functor preserves monomorphisms if it maps monomorphisms to monomorphisms. -/
class PreservesMonomorphisms (F : C ⥤ D) : Prop where
  preserves : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], Mono (F.map f)
#align category_theory.functor.preserves_monomorphisms CategoryTheory.Functor.PreservesMonomorphisms
-/

/- warning: category_theory.functor.map_mono -> CategoryTheory.Functor.map_mono is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_4 : CategoryTheory.Functor.PreservesMonomorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_5 : CategoryTheory.Mono.{u1, u3} C _inst_1 X Y f], CategoryTheory.Mono.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y f)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_4 : CategoryTheory.Functor.PreservesMonomorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_5 : CategoryTheory.Mono.{u1, u3} C _inst_1 X Y f], CategoryTheory.Mono.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y f)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_mono CategoryTheory.Functor.map_monoₓ'. -/
instance map_mono (F : C ⥤ D) [PreservesMonomorphisms F] {X Y : C} (f : X ⟶ Y) [Mono f] :
    Mono (F.map f) :=
  PreservesMonomorphisms.preserves f
#align category_theory.functor.map_mono CategoryTheory.Functor.map_mono

#print CategoryTheory.Functor.PreservesEpimorphisms /-
/-- A functor preserves epimorphisms if it maps epimorphisms to epimorphisms. -/
class PreservesEpimorphisms (F : C ⥤ D) : Prop where
  preserves : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], Epi (F.map f)
#align category_theory.functor.preserves_epimorphisms CategoryTheory.Functor.PreservesEpimorphisms
-/

/- warning: category_theory.functor.map_epi -> CategoryTheory.Functor.map_epi is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_4 : CategoryTheory.Functor.PreservesEpimorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_5 : CategoryTheory.Epi.{u1, u3} C _inst_1 X Y f], CategoryTheory.Epi.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y f)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_4 : CategoryTheory.Functor.PreservesEpimorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_5 : CategoryTheory.Epi.{u1, u3} C _inst_1 X Y f], CategoryTheory.Epi.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y f)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_epi CategoryTheory.Functor.map_epiₓ'. -/
instance map_epi (F : C ⥤ D) [PreservesEpimorphisms F] {X Y : C} (f : X ⟶ Y) [Epi f] :
    Epi (F.map f) :=
  PreservesEpimorphisms.preserves f
#align category_theory.functor.map_epi CategoryTheory.Functor.map_epi

#print CategoryTheory.Functor.ReflectsMonomorphisms /-
/-- A functor reflects monomorphisms if morphisms that are mapped to monomorphisms are themselves
    monomorphisms. -/
class ReflectsMonomorphisms (F : C ⥤ D) : Prop where
  reflects : ∀ {X Y : C} (f : X ⟶ Y), Mono (F.map f) → Mono f
#align category_theory.functor.reflects_monomorphisms CategoryTheory.Functor.ReflectsMonomorphisms
-/

/- warning: category_theory.functor.mono_of_mono_map -> CategoryTheory.Functor.mono_of_mono_map is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_4 : CategoryTheory.Functor.ReflectsMonomorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C} {Y : C} {f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y}, (CategoryTheory.Mono.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y f)) -> (CategoryTheory.Mono.{u1, u3} C _inst_1 X Y f)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_4 : CategoryTheory.Functor.ReflectsMonomorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C} {Y : C} {f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y}, (CategoryTheory.Mono.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y f)) -> (CategoryTheory.Mono.{u1, u3} C _inst_1 X Y f)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.mono_of_mono_map CategoryTheory.Functor.mono_of_mono_mapₓ'. -/
theorem mono_of_mono_map (F : C ⥤ D) [ReflectsMonomorphisms F] {X Y : C} {f : X ⟶ Y}
    (h : Mono (F.map f)) : Mono f :=
  ReflectsMonomorphisms.reflects f h
#align category_theory.functor.mono_of_mono_map CategoryTheory.Functor.mono_of_mono_map

#print CategoryTheory.Functor.ReflectsEpimorphisms /-
/-- A functor reflects epimorphisms if morphisms that are mapped to epimorphisms are themselves
    epimorphisms. -/
class ReflectsEpimorphisms (F : C ⥤ D) : Prop where
  reflects : ∀ {X Y : C} (f : X ⟶ Y), Epi (F.map f) → Epi f
#align category_theory.functor.reflects_epimorphisms CategoryTheory.Functor.ReflectsEpimorphisms
-/

/- warning: category_theory.functor.epi_of_epi_map -> CategoryTheory.Functor.epi_of_epi_map is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_4 : CategoryTheory.Functor.ReflectsEpimorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C} {Y : C} {f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y}, (CategoryTheory.Epi.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y f)) -> (CategoryTheory.Epi.{u1, u3} C _inst_1 X Y f)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_4 : CategoryTheory.Functor.ReflectsEpimorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] {X : C} {Y : C} {f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y}, (CategoryTheory.Epi.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y f)) -> (CategoryTheory.Epi.{u1, u3} C _inst_1 X Y f)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.epi_of_epi_map CategoryTheory.Functor.epi_of_epi_mapₓ'. -/
theorem epi_of_epi_map (F : C ⥤ D) [ReflectsEpimorphisms F] {X Y : C} {f : X ⟶ Y}
    (h : Epi (F.map f)) : Epi f :=
  ReflectsEpimorphisms.reflects f h
#align category_theory.functor.epi_of_epi_map CategoryTheory.Functor.epi_of_epi_map

#print CategoryTheory.Functor.preservesMonomorphisms_comp /-
instance preservesMonomorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [PreservesMonomorphisms F]
    [PreservesMonomorphisms G] : PreservesMonomorphisms (F ⋙ G)
    where preserves X Y f h := by rw [comp_map]; exact inferInstance
#align category_theory.functor.preserves_monomorphisms_comp CategoryTheory.Functor.preservesMonomorphisms_comp
-/

#print CategoryTheory.Functor.preservesEpimorphisms_comp /-
instance preservesEpimorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [PreservesEpimorphisms F]
    [PreservesEpimorphisms G] : PreservesEpimorphisms (F ⋙ G)
    where preserves X Y f h := by rw [comp_map]; exact inferInstance
#align category_theory.functor.preserves_epimorphisms_comp CategoryTheory.Functor.preservesEpimorphisms_comp
-/

#print CategoryTheory.Functor.reflectsMonomorphisms_comp /-
instance reflectsMonomorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [ReflectsMonomorphisms F]
    [ReflectsMonomorphisms G] : ReflectsMonomorphisms (F ⋙ G)
    where reflects X Y f h := F.mono_of_mono_map (G.mono_of_mono_map h)
#align category_theory.functor.reflects_monomorphisms_comp CategoryTheory.Functor.reflectsMonomorphisms_comp
-/

#print CategoryTheory.Functor.reflectsEpimorphisms_comp /-
instance reflectsEpimorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [ReflectsEpimorphisms F]
    [ReflectsEpimorphisms G] : ReflectsEpimorphisms (F ⋙ G)
    where reflects X Y f h := F.epi_of_epi_map (G.epi_of_epi_map h)
#align category_theory.functor.reflects_epimorphisms_comp CategoryTheory.Functor.reflectsEpimorphisms_comp
-/

#print CategoryTheory.Functor.preservesEpimorphisms_of_preserves_of_reflects /-
theorem preservesEpimorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [PreservesEpimorphisms (F ⋙ G)] [ReflectsEpimorphisms G] : PreservesEpimorphisms F :=
  ⟨fun X Y f hf => G.epi_of_epi_map <| show Epi ((F ⋙ G).map f) from inferInstance⟩
#align category_theory.functor.preserves_epimorphisms_of_preserves_of_reflects CategoryTheory.Functor.preservesEpimorphisms_of_preserves_of_reflects
-/

#print CategoryTheory.Functor.preservesMonomorphisms_of_preserves_of_reflects /-
theorem preservesMonomorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [PreservesMonomorphisms (F ⋙ G)] [ReflectsMonomorphisms G] : PreservesMonomorphisms F :=
  ⟨fun X Y f hf => G.mono_of_mono_map <| show Mono ((F ⋙ G).map f) from inferInstance⟩
#align category_theory.functor.preserves_monomorphisms_of_preserves_of_reflects CategoryTheory.Functor.preservesMonomorphisms_of_preserves_of_reflects
-/

#print CategoryTheory.Functor.reflectsEpimorphisms_of_preserves_of_reflects /-
theorem reflectsEpimorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [PreservesEpimorphisms G] [ReflectsEpimorphisms (F ⋙ G)] : ReflectsEpimorphisms F :=
  ⟨fun X Y f hf => (F ⋙ G).epi_of_epi_map <| show Epi (G.map (F.map f)) from inferInstance⟩
#align category_theory.functor.reflects_epimorphisms_of_preserves_of_reflects CategoryTheory.Functor.reflectsEpimorphisms_of_preserves_of_reflects
-/

#print CategoryTheory.Functor.reflectsMonomorphisms_of_preserves_of_reflects /-
theorem reflectsMonomorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [PreservesMonomorphisms G] [ReflectsMonomorphisms (F ⋙ G)] : ReflectsMonomorphisms F :=
  ⟨fun X Y f hf => (F ⋙ G).mono_of_mono_map <| show Mono (G.map (F.map f)) from inferInstance⟩
#align category_theory.functor.reflects_monomorphisms_of_preserves_of_reflects CategoryTheory.Functor.reflectsMonomorphisms_of_preserves_of_reflects
-/

#print CategoryTheory.Functor.preservesMonomorphisms.of_iso /-
theorem preservesMonomorphisms.of_iso {F G : C ⥤ D} [PreservesMonomorphisms F] (α : F ≅ G) :
    PreservesMonomorphisms G :=
  {
    preserves := fun X Y f h =>
      by
      haveI : mono (F.map f ≫ (α.app Y).Hom) := mono_comp _ _
      convert(mono_comp _ _ : mono ((α.app X).inv ≫ F.map f ≫ (α.app Y).Hom))
      rw [iso.eq_inv_comp, iso.app_hom, iso.app_hom, nat_trans.naturality] }
#align category_theory.functor.preserves_monomorphisms.of_iso CategoryTheory.Functor.preservesMonomorphisms.of_iso
-/

#print CategoryTheory.Functor.preservesMonomorphisms.iso_iff /-
theorem preservesMonomorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    PreservesMonomorphisms F ↔ PreservesMonomorphisms G :=
  ⟨fun h => preserves_monomorphisms.of_iso α, fun h => preserves_monomorphisms.of_iso α.symm⟩
#align category_theory.functor.preserves_monomorphisms.iso_iff CategoryTheory.Functor.preservesMonomorphisms.iso_iff
-/

#print CategoryTheory.Functor.preservesEpimorphisms.of_iso /-
theorem preservesEpimorphisms.of_iso {F G : C ⥤ D} [PreservesEpimorphisms F] (α : F ≅ G) :
    PreservesEpimorphisms G :=
  {
    preserves := fun X Y f h =>
      by
      haveI : epi (F.map f ≫ (α.app Y).Hom) := epi_comp _ _
      convert(epi_comp _ _ : epi ((α.app X).inv ≫ F.map f ≫ (α.app Y).Hom))
      rw [iso.eq_inv_comp, iso.app_hom, iso.app_hom, nat_trans.naturality] }
#align category_theory.functor.preserves_epimorphisms.of_iso CategoryTheory.Functor.preservesEpimorphisms.of_iso
-/

#print CategoryTheory.Functor.preservesEpimorphisms.iso_iff /-
theorem preservesEpimorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    PreservesEpimorphisms F ↔ PreservesEpimorphisms G :=
  ⟨fun h => preserves_epimorphisms.of_iso α, fun h => preserves_epimorphisms.of_iso α.symm⟩
#align category_theory.functor.preserves_epimorphisms.iso_iff CategoryTheory.Functor.preservesEpimorphisms.iso_iff
-/

#print CategoryTheory.Functor.reflectsMonomorphisms.of_iso /-
theorem reflectsMonomorphisms.of_iso {F G : C ⥤ D} [ReflectsMonomorphisms F] (α : F ≅ G) :
    ReflectsMonomorphisms G :=
  {
    reflects := fun X Y f h => by
      apply F.mono_of_mono_map
      haveI : mono (G.map f ≫ (α.app Y).inv) := mono_comp _ _
      convert(mono_comp _ _ : mono ((α.app X).Hom ≫ G.map f ≫ (α.app Y).inv))
      rw [← category.assoc, iso.eq_comp_inv, iso.app_hom, iso.app_hom, nat_trans.naturality] }
#align category_theory.functor.reflects_monomorphisms.of_iso CategoryTheory.Functor.reflectsMonomorphisms.of_iso
-/

#print CategoryTheory.Functor.reflectsMonomorphisms.iso_iff /-
theorem reflectsMonomorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    ReflectsMonomorphisms F ↔ ReflectsMonomorphisms G :=
  ⟨fun h => reflects_monomorphisms.of_iso α, fun h => reflects_monomorphisms.of_iso α.symm⟩
#align category_theory.functor.reflects_monomorphisms.iso_iff CategoryTheory.Functor.reflectsMonomorphisms.iso_iff
-/

#print CategoryTheory.Functor.reflectsEpimorphisms.of_iso /-
theorem reflectsEpimorphisms.of_iso {F G : C ⥤ D} [ReflectsEpimorphisms F] (α : F ≅ G) :
    ReflectsEpimorphisms G :=
  {
    reflects := fun X Y f h => by
      apply F.epi_of_epi_map
      haveI : epi (G.map f ≫ (α.app Y).inv) := epi_comp _ _
      convert(epi_comp _ _ : epi ((α.app X).Hom ≫ G.map f ≫ (α.app Y).inv))
      rw [← category.assoc, iso.eq_comp_inv, iso.app_hom, iso.app_hom, nat_trans.naturality] }
#align category_theory.functor.reflects_epimorphisms.of_iso CategoryTheory.Functor.reflectsEpimorphisms.of_iso
-/

#print CategoryTheory.Functor.reflectsEpimorphisms.iso_iff /-
theorem reflectsEpimorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    ReflectsEpimorphisms F ↔ ReflectsEpimorphisms G :=
  ⟨fun h => reflects_epimorphisms.of_iso α, fun h => reflects_epimorphisms.of_iso α.symm⟩
#align category_theory.functor.reflects_epimorphisms.iso_iff CategoryTheory.Functor.reflectsEpimorphisms.iso_iff
-/

#print CategoryTheory.Functor.preservesEpimorphsisms_of_adjunction /-
theorem preservesEpimorphsisms_of_adjunction {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    PreservesEpimorphisms F :=
  {
    preserves := fun X Y f hf =>
      ⟨by
        intro Z g h H
        replace H := congr_arg (adj.hom_equiv X Z) H
        rwa [adj.hom_equiv_naturality_left, adj.hom_equiv_naturality_left, cancel_epi,
          Equiv.apply_eq_iff_eq] at H⟩ }
#align category_theory.functor.preserves_epimorphsisms_of_adjunction CategoryTheory.Functor.preservesEpimorphsisms_of_adjunction
-/

#print CategoryTheory.Functor.preservesEpimorphisms_of_isLeftAdjoint /-
instance (priority := 100) preservesEpimorphisms_of_isLeftAdjoint (F : C ⥤ D) [IsLeftAdjoint F] :
    PreservesEpimorphisms F :=
  preservesEpimorphsisms_of_adjunction (Adjunction.ofLeftAdjoint F)
#align category_theory.functor.preserves_epimorphisms_of_is_left_adjoint CategoryTheory.Functor.preservesEpimorphisms_of_isLeftAdjoint
-/

#print CategoryTheory.Functor.preservesMonomorphisms_of_adjunction /-
theorem preservesMonomorphisms_of_adjunction {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    PreservesMonomorphisms G :=
  {
    preserves := fun X Y f hf =>
      ⟨by
        intro Z g h H
        replace H := congr_arg (adj.hom_equiv Z Y).symm H
        rwa [adj.hom_equiv_naturality_right_symm, adj.hom_equiv_naturality_right_symm, cancel_mono,
          Equiv.apply_eq_iff_eq] at H⟩ }
#align category_theory.functor.preserves_monomorphisms_of_adjunction CategoryTheory.Functor.preservesMonomorphisms_of_adjunction
-/

#print CategoryTheory.Functor.preservesMonomorphisms_of_isRightAdjoint /-
instance (priority := 100) preservesMonomorphisms_of_isRightAdjoint (F : C ⥤ D) [IsRightAdjoint F] :
    PreservesMonomorphisms F :=
  preservesMonomorphisms_of_adjunction (Adjunction.ofRightAdjoint F)
#align category_theory.functor.preserves_monomorphisms_of_is_right_adjoint CategoryTheory.Functor.preservesMonomorphisms_of_isRightAdjoint
-/

#print CategoryTheory.Functor.reflectsMonomorphisms_of_faithful /-
instance (priority := 100) reflectsMonomorphisms_of_faithful (F : C ⥤ D) [Faithful F] :
    ReflectsMonomorphisms F
    where reflects X Y f hf :=
    ⟨fun Z g h hgh =>
      F.map_injective ((cancel_mono (F.map f)).1 (by rw [← F.map_comp, hgh, F.map_comp]))⟩
#align category_theory.functor.reflects_monomorphisms_of_faithful CategoryTheory.Functor.reflectsMonomorphisms_of_faithful
-/

#print CategoryTheory.Functor.reflectsEpimorphisms_of_faithful /-
instance (priority := 100) reflectsEpimorphisms_of_faithful (F : C ⥤ D) [Faithful F] :
    ReflectsEpimorphisms F
    where reflects X Y f hf :=
    ⟨fun Z g h hgh =>
      F.map_injective ((cancel_epi (F.map f)).1 (by rw [← F.map_comp, hgh, F.map_comp]))⟩
#align category_theory.functor.reflects_epimorphisms_of_faithful CategoryTheory.Functor.reflectsEpimorphisms_of_faithful
-/

section

variable (F : C ⥤ D) {X Y : C} (f : X ⟶ Y)

/- warning: category_theory.functor.split_epi_equiv -> CategoryTheory.Functor.splitEpiEquiv is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_4 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [_inst_5 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F], Equiv.{succ u1, succ u2} (CategoryTheory.SplitEpi.{u1, u3} C _inst_1 X Y f) (CategoryTheory.SplitEpi.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y f))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_4 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [_inst_5 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F], Equiv.{succ u1, succ u2} (CategoryTheory.SplitEpi.{u1, u3} C _inst_1 X Y f) (CategoryTheory.SplitEpi.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y f))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.split_epi_equiv CategoryTheory.Functor.splitEpiEquivₓ'. -/
/-- If `F` is a fully faithful functor, split epimorphisms are preserved and reflected by `F`. -/
def splitEpiEquiv [Full F] [Faithful F] : SplitEpi f ≃ SplitEpi (F.map f)
    where
  toFun f := f.map F
  invFun s := by
    refine' ⟨F.preimage s.section_, _⟩
    apply F.map_injective
    simp only [map_comp, image_preimage, map_id]
    apply split_epi.id
  left_inv := by tidy
  right_inv := by tidy
#align category_theory.functor.split_epi_equiv CategoryTheory.Functor.splitEpiEquiv

/- warning: category_theory.functor.is_split_epi_iff -> CategoryTheory.Functor.isSplitEpi_iff is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_4 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [_inst_5 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F], Iff (CategoryTheory.IsSplitEpi.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y f)) (CategoryTheory.IsSplitEpi.{u1, u3} C _inst_1 X Y f)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_4 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [_inst_5 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F], Iff (CategoryTheory.IsSplitEpi.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y f)) (CategoryTheory.IsSplitEpi.{u1, u3} C _inst_1 X Y f)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.is_split_epi_iff CategoryTheory.Functor.isSplitEpi_iffₓ'. -/
@[simp]
theorem isSplitEpi_iff [Full F] [Faithful F] : IsSplitEpi (F.map f) ↔ IsSplitEpi f :=
  by
  constructor
  · intro h; exact is_split_epi.mk' ((split_epi_equiv F f).invFun h.exists_split_epi.some)
  · intro h; exact is_split_epi.mk' ((split_epi_equiv F f).toFun h.exists_split_epi.some)
#align category_theory.functor.is_split_epi_iff CategoryTheory.Functor.isSplitEpi_iff

/- warning: category_theory.functor.split_mono_equiv -> CategoryTheory.Functor.splitMonoEquiv is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_4 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [_inst_5 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F], Equiv.{succ u1, succ u2} (CategoryTheory.SplitMono.{u1, u3} C _inst_1 X Y f) (CategoryTheory.SplitMono.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y f))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_4 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [_inst_5 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F], Equiv.{succ u1, succ u2} (CategoryTheory.SplitMono.{u1, u3} C _inst_1 X Y f) (CategoryTheory.SplitMono.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y f))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.split_mono_equiv CategoryTheory.Functor.splitMonoEquivₓ'. -/
/-- If `F` is a fully faithful functor, split monomorphisms are preserved and reflected by `F`. -/
def splitMonoEquiv [Full F] [Faithful F] : SplitMono f ≃ SplitMono (F.map f)
    where
  toFun f := f.map F
  invFun s := by
    refine' ⟨F.preimage s.retraction, _⟩
    apply F.map_injective
    simp only [map_comp, image_preimage, map_id]
    apply split_mono.id
  left_inv := by tidy
  right_inv := by tidy
#align category_theory.functor.split_mono_equiv CategoryTheory.Functor.splitMonoEquiv

/- warning: category_theory.functor.is_split_mono_iff -> CategoryTheory.Functor.isSplitMono_iff is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_4 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [_inst_5 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F], Iff (CategoryTheory.IsSplitMono.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y f)) (CategoryTheory.IsSplitMono.{u1, u3} C _inst_1 X Y f)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [_inst_4 : CategoryTheory.Full.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [_inst_5 : CategoryTheory.Faithful.{u1, u2, u3, u4} C _inst_1 D _inst_2 F], Iff (CategoryTheory.IsSplitMono.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y f)) (CategoryTheory.IsSplitMono.{u1, u3} C _inst_1 X Y f)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.is_split_mono_iff CategoryTheory.Functor.isSplitMono_iffₓ'. -/
@[simp]
theorem isSplitMono_iff [Full F] [Faithful F] : IsSplitMono (F.map f) ↔ IsSplitMono f :=
  by
  constructor
  · intro h; exact is_split_mono.mk' ((split_mono_equiv F f).invFun h.exists_split_mono.some)
  · intro h; exact is_split_mono.mk' ((split_mono_equiv F f).toFun h.exists_split_mono.some)
#align category_theory.functor.is_split_mono_iff CategoryTheory.Functor.isSplitMono_iff

/- warning: category_theory.functor.epi_map_iff_epi -> CategoryTheory.Functor.epi_map_iff_epi is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [hF₁ : CategoryTheory.Functor.PreservesEpimorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [hF₂ : CategoryTheory.Functor.ReflectsEpimorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 F], Iff (CategoryTheory.Epi.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y f)) (CategoryTheory.Epi.{u1, u3} C _inst_1 X Y f)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [hF₁ : CategoryTheory.Functor.PreservesEpimorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [hF₂ : CategoryTheory.Functor.ReflectsEpimorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 F], Iff (CategoryTheory.Epi.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y f)) (CategoryTheory.Epi.{u1, u3} C _inst_1 X Y f)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.epi_map_iff_epi CategoryTheory.Functor.epi_map_iff_epiₓ'. -/
@[simp]
theorem epi_map_iff_epi [hF₁ : PreservesEpimorphisms F] [hF₂ : ReflectsEpimorphisms F] :
    Epi (F.map f) ↔ Epi f := by
  constructor
  · exact F.epi_of_epi_map
  · intro h
    exact F.map_epi f
#align category_theory.functor.epi_map_iff_epi CategoryTheory.Functor.epi_map_iff_epi

/- warning: category_theory.functor.mono_map_iff_mono -> CategoryTheory.Functor.mono_map_iff_mono is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [hF₁ : CategoryTheory.Functor.PreservesMonomorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [hF₂ : CategoryTheory.Functor.ReflectsMonomorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 F], Iff (CategoryTheory.Mono.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y f)) (CategoryTheory.Mono.{u1, u3} C _inst_1 X Y f)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y) [hF₁ : CategoryTheory.Functor.PreservesMonomorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 F] [hF₂ : CategoryTheory.Functor.ReflectsMonomorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 F], Iff (CategoryTheory.Mono.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y f)) (CategoryTheory.Mono.{u1, u3} C _inst_1 X Y f)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.mono_map_iff_mono CategoryTheory.Functor.mono_map_iff_monoₓ'. -/
@[simp]
theorem mono_map_iff_mono [hF₁ : PreservesMonomorphisms F] [hF₂ : ReflectsMonomorphisms F] :
    Mono (F.map f) ↔ Mono f := by
  constructor
  · exact F.mono_of_mono_map
  · intro h
    exact F.map_mono f
#align category_theory.functor.mono_map_iff_mono CategoryTheory.Functor.mono_map_iff_mono

#print CategoryTheory.Functor.splitEpiCategoryImpOfIsEquivalence /-
/-- If `F : C ⥤ D` is an equivalence of categories and `C` is a `split_epi_category`,
then `D` also is. -/
def splitEpiCategoryImpOfIsEquivalence [IsEquivalence F] [SplitEpiCategory C] :
    SplitEpiCategory D :=
  ⟨fun X Y f => by
    intro
    rw [← F.inv.is_split_epi_iff f]
    apply is_split_epi_of_epi⟩
#align category_theory.functor.split_epi_category_imp_of_is_equivalence CategoryTheory.Functor.splitEpiCategoryImpOfIsEquivalence
-/

end

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C D : Type _} [Category C] [Category D] {F : C ⥤ D} {F' : D ⥤ C} {A B : C}

/- warning: category_theory.adjunction.strong_epi_map_of_strong_epi -> CategoryTheory.Adjunction.strongEpi_map_of_strongEpi is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] {F : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2} {F' : CategoryTheory.Functor.{u4, u3, u2, u1} D _inst_2 C _inst_1} {A : C} {B : C}, (CategoryTheory.Adjunction.{u3, u4, u1, u2} C _inst_1 D _inst_2 F F') -> (forall (f : Quiver.Hom.{succ u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) A B) [h₁ : CategoryTheory.Functor.PreservesMonomorphisms.{u4, u3, u2, u1} D _inst_2 C _inst_1 F'] [h₂ : CategoryTheory.Functor.PreservesEpimorphisms.{u3, u4, u1, u2} C _inst_1 D _inst_2 F] [_inst_3 : CategoryTheory.StrongEpi.{u3, u1} C _inst_1 A B f], CategoryTheory.StrongEpi.{u4, u2} D _inst_2 (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 F A) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 F B) (CategoryTheory.Functor.map.{u3, u4, u1, u2} C _inst_1 D _inst_2 F A B f))
but is expected to have type
  forall {C : Type.{u2}} {D : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u4, u2} C] [_inst_2 : CategoryTheory.Category.{u3, u1} D] {F : CategoryTheory.Functor.{u4, u3, u2, u1} C _inst_1 D _inst_2} {F' : CategoryTheory.Functor.{u3, u4, u1, u2} D _inst_2 C _inst_1} {A : C} {B : C}, (CategoryTheory.Adjunction.{u4, u3, u2, u1} C _inst_1 D _inst_2 F F') -> (forall (f : Quiver.Hom.{succ u4, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_1)) A B) [h₁ : CategoryTheory.Functor.PreservesMonomorphisms.{u3, u4, u1, u2} D _inst_2 C _inst_1 F'] [h₂ : CategoryTheory.Functor.PreservesEpimorphisms.{u4, u3, u2, u1} C _inst_1 D _inst_2 F] [_inst_3 : CategoryTheory.StrongEpi.{u4, u2} C _inst_1 A B f], CategoryTheory.StrongEpi.{u3, u1} D _inst_2 (Prefunctor.obj.{succ u4, succ u3, u2, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} D (CategoryTheory.Category.toCategoryStruct.{u3, u1} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u4, u3, u2, u1} C _inst_1 D _inst_2 F) A) (Prefunctor.obj.{succ u4, succ u3, u2, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} D (CategoryTheory.Category.toCategoryStruct.{u3, u1} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u4, u3, u2, u1} C _inst_1 D _inst_2 F) B) (Prefunctor.map.{succ u4, succ u3, u2, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} D (CategoryTheory.Category.toCategoryStruct.{u3, u1} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u4, u3, u2, u1} C _inst_1 D _inst_2 F) A B f))
Case conversion may be inaccurate. Consider using '#align category_theory.adjunction.strong_epi_map_of_strong_epi CategoryTheory.Adjunction.strongEpi_map_of_strongEpiₓ'. -/
theorem strongEpi_map_of_strongEpi (adj : F ⊣ F') (f : A ⟶ B) [h₁ : F'.PreservesMonomorphisms]
    [h₂ : F.PreservesEpimorphisms] [StrongEpi f] : StrongEpi (F.map f) :=
  ⟨inferInstance, fun X Y Z => by intro ; rw [adj.has_lifting_property_iff]; infer_instance⟩
#align category_theory.adjunction.strong_epi_map_of_strong_epi CategoryTheory.Adjunction.strongEpi_map_of_strongEpi

/- warning: category_theory.adjunction.strong_epi_map_of_is_equivalence -> CategoryTheory.Adjunction.strongEpi_map_of_isEquivalence is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] {F : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2} {A : C} {B : C} [_inst_3 : CategoryTheory.IsEquivalence.{u3, u4, u1, u2} C _inst_1 D _inst_2 F] (f : Quiver.Hom.{succ u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) A B) [h : CategoryTheory.StrongEpi.{u3, u1} C _inst_1 A B f], CategoryTheory.StrongEpi.{u4, u2} D _inst_2 (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 F A) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 F B) (CategoryTheory.Functor.map.{u3, u4, u1, u2} C _inst_1 D _inst_2 F A B f)
but is expected to have type
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] {F : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2} {A : C} {B : C} [_inst_3 : CategoryTheory.IsEquivalence.{u3, u4, u1, u2} C _inst_1 D _inst_2 F] (f : Quiver.Hom.{succ u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) A B) [h : CategoryTheory.StrongEpi.{u3, u1} C _inst_1 A B f], CategoryTheory.StrongEpi.{u4, u2} D _inst_2 (Prefunctor.obj.{succ u3, succ u4, u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} C _inst_1 D _inst_2 F) A) (Prefunctor.obj.{succ u3, succ u4, u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} C _inst_1 D _inst_2 F) B) (Prefunctor.map.{succ u3, succ u4, u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} C _inst_1 D _inst_2 F) A B f)
Case conversion may be inaccurate. Consider using '#align category_theory.adjunction.strong_epi_map_of_is_equivalence CategoryTheory.Adjunction.strongEpi_map_of_isEquivalenceₓ'. -/
instance strongEpi_map_of_isEquivalence [IsEquivalence F] (f : A ⟶ B) [h : StrongEpi f] :
    StrongEpi (F.map f) :=
  F.asEquivalence.toAdjunction.strongEpi_map_of_strongEpi f
#align category_theory.adjunction.strong_epi_map_of_is_equivalence CategoryTheory.Adjunction.strongEpi_map_of_isEquivalence

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

variable {C D : Type _} [Category C] [Category D] {F : C ⥤ D} {A B : C} (f : A ⟶ B)

/- warning: category_theory.functor.strong_epi_map_iff_strong_epi_of_is_equivalence -> CategoryTheory.Functor.strongEpi_map_iff_strongEpi_of_isEquivalence is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] {F : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2} {A : C} {B : C} (f : Quiver.Hom.{succ u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) A B) [_inst_3 : CategoryTheory.IsEquivalence.{u3, u4, u1, u2} C _inst_1 D _inst_2 F], Iff (CategoryTheory.StrongEpi.{u4, u2} D _inst_2 (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 F A) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 F B) (CategoryTheory.Functor.map.{u3, u4, u1, u2} C _inst_1 D _inst_2 F A B f)) (CategoryTheory.StrongEpi.{u3, u1} C _inst_1 A B f)
but is expected to have type
  forall {C : Type.{u2}} {D : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u4, u2} C] [_inst_2 : CategoryTheory.Category.{u3, u1} D] {F : CategoryTheory.Functor.{u4, u3, u2, u1} C _inst_1 D _inst_2} {A : C} {B : C} (f : Quiver.Hom.{succ u4, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_1)) A B) [_inst_3 : CategoryTheory.IsEquivalence.{u4, u3, u2, u1} C _inst_1 D _inst_2 F], Iff (CategoryTheory.StrongEpi.{u3, u1} D _inst_2 (Prefunctor.obj.{succ u4, succ u3, u2, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} D (CategoryTheory.Category.toCategoryStruct.{u3, u1} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u4, u3, u2, u1} C _inst_1 D _inst_2 F) A) (Prefunctor.obj.{succ u4, succ u3, u2, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} D (CategoryTheory.Category.toCategoryStruct.{u3, u1} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u4, u3, u2, u1} C _inst_1 D _inst_2 F) B) (Prefunctor.map.{succ u4, succ u3, u2, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} D (CategoryTheory.Category.toCategoryStruct.{u3, u1} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u4, u3, u2, u1} C _inst_1 D _inst_2 F) A B f)) (CategoryTheory.StrongEpi.{u4, u2} C _inst_1 A B f)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.strong_epi_map_iff_strong_epi_of_is_equivalence CategoryTheory.Functor.strongEpi_map_iff_strongEpi_of_isEquivalenceₓ'. -/
@[simp]
theorem strongEpi_map_iff_strongEpi_of_isEquivalence [IsEquivalence F] :
    StrongEpi (F.map f) ↔ StrongEpi f := by
  constructor
  · intro
    have e : arrow.mk f ≅ arrow.mk (F.inv.map (F.map f)) :=
      arrow.iso_of_nat_iso F.as_equivalence.unit_iso (arrow.mk f)
    rw [strong_epi.iff_of_arrow_iso e]
    infer_instance
  · intro
    infer_instance
#align category_theory.functor.strong_epi_map_iff_strong_epi_of_is_equivalence CategoryTheory.Functor.strongEpi_map_iff_strongEpi_of_isEquivalence

end CategoryTheory.Functor

