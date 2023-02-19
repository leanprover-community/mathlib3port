/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Scott Morrison

! This file was ported from Lean 3 source module category_theory.epi_mono
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Opposites
import Mathbin.CategoryTheory.Groupoid

/-!
# Facts about epimorphisms and monomorphisms.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The definitions of `epi` and `mono` are in `category_theory.category`,
since they are used by some lemmas for `iso`, which is used everywhere.
-/


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

#print CategoryTheory.unop_mono_of_epi /-
instance unop_mono_of_epi {A B : Cᵒᵖ} (f : A ⟶ B) [Epi f] : Mono f.unop :=
  ⟨fun Z g h eq => Quiver.Hom.op_inj ((cancel_epi f).1 (Quiver.Hom.unop_inj Eq))⟩
#align category_theory.unop_mono_of_epi CategoryTheory.unop_mono_of_epi
-/

#print CategoryTheory.unop_epi_of_mono /-
instance unop_epi_of_mono {A B : Cᵒᵖ} (f : A ⟶ B) [Mono f] : Epi f.unop :=
  ⟨fun Z g h eq => Quiver.Hom.op_inj ((cancel_mono f).1 (Quiver.Hom.unop_inj Eq))⟩
#align category_theory.unop_epi_of_mono CategoryTheory.unop_epi_of_mono
-/

#print CategoryTheory.op_mono_of_epi /-
instance op_mono_of_epi {A B : C} (f : A ⟶ B) [Epi f] : Mono f.op :=
  ⟨fun Z g h eq => Quiver.Hom.unop_inj ((cancel_epi f).1 (Quiver.Hom.op_inj Eq))⟩
#align category_theory.op_mono_of_epi CategoryTheory.op_mono_of_epi
-/

#print CategoryTheory.op_epi_of_mono /-
instance op_epi_of_mono {A B : C} (f : A ⟶ B) [Mono f] : Epi f.op :=
  ⟨fun Z g h eq => Quiver.Hom.unop_inj ((cancel_mono f).1 (Quiver.Hom.op_inj Eq))⟩
#align category_theory.op_epi_of_mono CategoryTheory.op_epi_of_mono
-/

#print CategoryTheory.SplitMono /-
/-- A split monomorphism is a morphism `f : X ⟶ Y` with a given retraction `retraction f : Y ⟶ X`
such that `f ≫ retraction f = 𝟙 X`.

Every split monomorphism is a monomorphism.
-/
@[ext, nolint has_nonempty_instance]
structure SplitMono {X Y : C} (f : X ⟶ Y) where
  retraction : Y ⟶ X
  id' : f ≫ retraction = 𝟙 X := by obviously
#align category_theory.split_mono CategoryTheory.SplitMono
-/

restate_axiom split_mono.id'

attribute [simp, reassoc.1] split_mono.id

#print CategoryTheory.IsSplitMono /-
/-- `is_split_mono f` is the assertion that `f` admits a retraction -/
class IsSplitMono {X Y : C} (f : X ⟶ Y) : Prop where
  exists_splitMono : Nonempty (SplitMono f)
#align category_theory.is_split_mono CategoryTheory.IsSplitMono
-/

#print CategoryTheory.IsSplitMono.mk' /-
/-- A constructor for `is_split_mono f` taking a `split_mono f` as an argument -/
theorem IsSplitMono.mk' {X Y : C} {f : X ⟶ Y} (sm : SplitMono f) : IsSplitMono f :=
  ⟨Nonempty.intro sm⟩
#align category_theory.is_split_mono.mk' CategoryTheory.IsSplitMono.mk'
-/

#print CategoryTheory.SplitEpi /-
/-- A split epimorphism is a morphism `f : X ⟶ Y` with a given section `section_ f : Y ⟶ X`
such that `section_ f ≫ f = 𝟙 Y`.
(Note that `section` is a reserved keyword, so we append an underscore.)

Every split epimorphism is an epimorphism.
-/
@[ext, nolint has_nonempty_instance]
structure SplitEpi {X Y : C} (f : X ⟶ Y) where
  section_ : Y ⟶ X
  id' : section_ ≫ f = 𝟙 Y := by obviously
#align category_theory.split_epi CategoryTheory.SplitEpi
-/

restate_axiom split_epi.id'

attribute [simp, reassoc.1] split_epi.id

#print CategoryTheory.IsSplitEpi /-
/-- `is_split_epi f` is the assertion that `f` admits a section -/
class IsSplitEpi {X Y : C} (f : X ⟶ Y) : Prop where
  exists_splitEpi : Nonempty (SplitEpi f)
#align category_theory.is_split_epi CategoryTheory.IsSplitEpi
-/

#print CategoryTheory.IsSplitEpi.mk' /-
/-- A constructor for `is_split_epi f` taking a `split_epi f` as an argument -/
theorem IsSplitEpi.mk' {X Y : C} {f : X ⟶ Y} (se : SplitEpi f) : IsSplitEpi f :=
  ⟨Nonempty.intro se⟩
#align category_theory.is_split_epi.mk' CategoryTheory.IsSplitEpi.mk'
-/

#print CategoryTheory.retraction /-
/-- The chosen retraction of a split monomorphism. -/
noncomputable def retraction {X Y : C} (f : X ⟶ Y) [hf : IsSplitMono f] : Y ⟶ X :=
  hf.exists_splitMono.some.retraction
#align category_theory.retraction CategoryTheory.retraction
-/

#print CategoryTheory.IsSplitMono.id /-
@[simp, reassoc.1]
theorem IsSplitMono.id {X Y : C} (f : X ⟶ Y) [hf : IsSplitMono f] : f ≫ retraction f = 𝟙 X :=
  hf.exists_splitMono.some.id
#align category_theory.is_split_mono.id CategoryTheory.IsSplitMono.id
-/

#print CategoryTheory.SplitMono.splitEpi /-
/-- The retraction of a split monomorphism has an obvious section. -/
def SplitMono.splitEpi {X Y : C} {f : X ⟶ Y} (sm : SplitMono f) : SplitEpi sm.retraction
    where section_ := f
#align category_theory.split_mono.split_epi CategoryTheory.SplitMono.splitEpi
-/

#print CategoryTheory.retraction_isSplitEpi /-
/-- The retraction of a split monomorphism is itself a split epimorphism. -/
instance retraction_isSplitEpi {X Y : C} (f : X ⟶ Y) [hf : IsSplitMono f] :
    IsSplitEpi (retraction f) :=
  IsSplitEpi.mk' (SplitMono.splitEpi _)
#align category_theory.retraction_is_split_epi CategoryTheory.retraction_isSplitEpi
-/

#print CategoryTheory.isIso_of_epi_of_isSplitMono /-
/-- A split mono which is epi is an iso. -/
theorem isIso_of_epi_of_isSplitMono {X Y : C} (f : X ⟶ Y) [IsSplitMono f] [Epi f] : IsIso f :=
  ⟨⟨retraction f, ⟨by simp, by simp [← cancel_epi f]⟩⟩⟩
#align category_theory.is_iso_of_epi_of_is_split_mono CategoryTheory.isIso_of_epi_of_isSplitMono
-/

#print CategoryTheory.section_ /-
/-- The chosen section of a split epimorphism.
(Note that `section` is a reserved keyword, so we append an underscore.)
-/
noncomputable def section_ {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] : Y ⟶ X :=
  hf.exists_splitEpi.some.section_
#align category_theory.section_ CategoryTheory.section_
-/

#print CategoryTheory.IsSplitEpi.id /-
@[simp, reassoc.1]
theorem IsSplitEpi.id {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] : section_ f ≫ f = 𝟙 Y :=
  hf.exists_splitEpi.some.id
#align category_theory.is_split_epi.id CategoryTheory.IsSplitEpi.id
-/

#print CategoryTheory.SplitEpi.splitMono /-
/-- The section of a split epimorphism has an obvious retraction. -/
def SplitEpi.splitMono {X Y : C} {f : X ⟶ Y} (se : SplitEpi f) : SplitMono se.section_
    where retraction := f
#align category_theory.split_epi.split_mono CategoryTheory.SplitEpi.splitMono
-/

#print CategoryTheory.section_isSplitMono /-
/-- The section of a split epimorphism is itself a split monomorphism. -/
instance section_isSplitMono {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] : IsSplitMono (section_ f) :=
  IsSplitMono.mk' (SplitEpi.splitMono _)
#align category_theory.section_is_split_mono CategoryTheory.section_isSplitMono
-/

#print CategoryTheory.isIso_of_mono_of_isSplitEpi /-
/-- A split epi which is mono is an iso. -/
theorem isIso_of_mono_of_isSplitEpi {X Y : C} (f : X ⟶ Y) [Mono f] [IsSplitEpi f] : IsIso f :=
  ⟨⟨section_ f, ⟨by simp [← cancel_mono f], by simp⟩⟩⟩
#align category_theory.is_iso_of_mono_of_is_split_epi CategoryTheory.isIso_of_mono_of_isSplitEpi
-/

#print CategoryTheory.IsSplitMono.of_iso /-
/-- Every iso is a split mono. -/
instance (priority := 100) IsSplitMono.of_iso {X Y : C} (f : X ⟶ Y) [IsIso f] : IsSplitMono f :=
  IsSplitMono.mk' { retraction := inv f }
#align category_theory.is_split_mono.of_iso CategoryTheory.IsSplitMono.of_iso
-/

#print CategoryTheory.IsSplitEpi.of_iso /-
/-- Every iso is a split epi. -/
instance (priority := 100) IsSplitEpi.of_iso {X Y : C} (f : X ⟶ Y) [IsIso f] : IsSplitEpi f :=
  IsSplitEpi.mk' { section_ := inv f }
#align category_theory.is_split_epi.of_iso CategoryTheory.IsSplitEpi.of_iso
-/

#print CategoryTheory.SplitMono.mono /-
theorem SplitMono.mono {X Y : C} {f : X ⟶ Y} (sm : SplitMono f) : Mono f :=
  { right_cancellation := fun Z g h w => by replace w := w =≫ sm.retraction; simpa using w }
#align category_theory.split_mono.mono CategoryTheory.SplitMono.mono
-/

#print CategoryTheory.IsSplitMono.mono /-
/-- Every split mono is a mono. -/
instance (priority := 100) IsSplitMono.mono {X Y : C} (f : X ⟶ Y) [hf : IsSplitMono f] : Mono f :=
  hf.exists_splitMono.some.Mono
#align category_theory.is_split_mono.mono CategoryTheory.IsSplitMono.mono
-/

#print CategoryTheory.SplitEpi.epi /-
theorem SplitEpi.epi {X Y : C} {f : X ⟶ Y} (se : SplitEpi f) : Epi f :=
  { left_cancellation := fun Z g h w => by replace w := se.section_ ≫= w; simpa using w }
#align category_theory.split_epi.epi CategoryTheory.SplitEpi.epi
-/

#print CategoryTheory.IsSplitEpi.epi /-
/-- Every split epi is an epi. -/
instance (priority := 100) IsSplitEpi.epi {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] : Epi f :=
  hf.exists_splitEpi.some.Epi
#align category_theory.is_split_epi.epi CategoryTheory.IsSplitEpi.epi
-/

#print CategoryTheory.IsIso.of_mono_retraction' /-
/-- Every split mono whose retraction is mono is an iso. -/
theorem IsIso.of_mono_retraction' {X Y : C} {f : X ⟶ Y} (hf : SplitMono f) [Mono <| hf.retraction] :
    IsIso f :=
  ⟨⟨hf.retraction, ⟨by simp, (cancel_mono_id <| hf.retraction).mp (by simp)⟩⟩⟩
#align category_theory.is_iso.of_mono_retraction' CategoryTheory.IsIso.of_mono_retraction'
-/

#print CategoryTheory.IsIso.of_mono_retraction /-
/-- Every split mono whose retraction is mono is an iso. -/
theorem IsIso.of_mono_retraction {X Y : C} (f : X ⟶ Y) [hf : IsSplitMono f]
    [hf' : Mono <| retraction f] : IsIso f :=
  @IsIso.of_mono_retraction' _ _ _ _ _ hf.exists_splitMono.some hf'
#align category_theory.is_iso.of_mono_retraction CategoryTheory.IsIso.of_mono_retraction
-/

#print CategoryTheory.IsIso.of_epi_section' /-
/-- Every split epi whose section is epi is an iso. -/
theorem IsIso.of_epi_section' {X Y : C} {f : X ⟶ Y} (hf : SplitEpi f) [Epi <| hf.section_] :
    IsIso f :=
  ⟨⟨hf.section_, ⟨(cancel_epi_id <| hf.section_).mp (by simp), by simp⟩⟩⟩
#align category_theory.is_iso.of_epi_section' CategoryTheory.IsIso.of_epi_section'
-/

#print CategoryTheory.IsIso.of_epi_section /-
/-- Every split epi whose section is epi is an iso. -/
theorem IsIso.of_epi_section {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] [hf' : Epi <| section_ f] :
    IsIso f :=
  @IsIso.of_epi_section' _ _ _ _ _ hf.exists_splitEpi.some hf'
#align category_theory.is_iso.of_epi_section CategoryTheory.IsIso.of_epi_section
-/

#print CategoryTheory.Groupoid.ofTruncSplitMono /-
-- FIXME this has unnecessarily become noncomputable!
/-- A category where every morphism has a `trunc` retraction is computably a groupoid. -/
noncomputable def Groupoid.ofTruncSplitMono
    (all_split_mono : ∀ {X Y : C} (f : X ⟶ Y), Trunc (IsSplitMono f)) : Groupoid.{v₁} C :=
  by
  apply groupoid.of_is_iso
  intro X Y f
  trunc_cases all_split_mono f
  trunc_cases all_split_mono (retraction f)
  apply is_iso.of_mono_retraction
#align category_theory.groupoid.of_trunc_split_mono CategoryTheory.Groupoid.ofTruncSplitMono
-/

section

variable (C)

#print CategoryTheory.SplitMonoCategory /-
/-- A split mono category is a category in which every monomorphism is split. -/
class SplitMonoCategory where
  isSplitMono_of_mono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], IsSplitMono f
#align category_theory.split_mono_category CategoryTheory.SplitMonoCategory
-/

#print CategoryTheory.SplitEpiCategory /-
/-- A split epi category is a category in which every epimorphism is split. -/
class SplitEpiCategory where
  isSplitEpi_of_epi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], IsSplitEpi f
#align category_theory.split_epi_category CategoryTheory.SplitEpiCategory
-/

end

#print CategoryTheory.isSplitMono_of_mono /-
/-- In a category in which every monomorphism is split, every monomorphism splits. This is not an
    instance because it would create an instance loop. -/
theorem isSplitMono_of_mono [SplitMonoCategory C] {X Y : C} (f : X ⟶ Y) [Mono f] : IsSplitMono f :=
  SplitMonoCategory.isSplitMono_of_mono _
#align category_theory.is_split_mono_of_mono CategoryTheory.isSplitMono_of_mono
-/

#print CategoryTheory.isSplitEpi_of_epi /-
/-- In a category in which every epimorphism is split, every epimorphism splits. This is not an
    instance because it would create an instance loop. -/
theorem isSplitEpi_of_epi [SplitEpiCategory C] {X Y : C} (f : X ⟶ Y) [Epi f] : IsSplitEpi f :=
  SplitEpiCategory.isSplitEpi_of_epi _
#align category_theory.is_split_epi_of_epi CategoryTheory.isSplitEpi_of_epi
-/

section

variable {D : Type u₂} [Category.{v₂} D]

/- warning: category_theory.split_mono.map -> CategoryTheory.SplitMono.map is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {X : C} {Y : C} {f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y}, (CategoryTheory.SplitMono.{u1, u3} C _inst_1 X Y f) -> (forall (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2), CategoryTheory.SplitMono.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y f))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {X : C} {Y : C} {f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y}, (CategoryTheory.SplitMono.{u1, u3} C _inst_1 X Y f) -> (forall (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2), CategoryTheory.SplitMono.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y f))
Case conversion may be inaccurate. Consider using '#align category_theory.split_mono.map CategoryTheory.SplitMono.mapₓ'. -/
/-- Split monomorphisms are also absolute monomorphisms. -/
@[simps]
def SplitMono.map {X Y : C} {f : X ⟶ Y} (sm : SplitMono f) (F : C ⥤ D) : SplitMono (F.map f)
    where
  retraction := F.map sm.retraction
  id' := by rw [← functor.map_comp, split_mono.id, Functor.map_id]
#align category_theory.split_mono.map CategoryTheory.SplitMono.map

/- warning: category_theory.split_epi.map -> CategoryTheory.SplitEpi.map is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {X : C} {Y : C} {f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y}, (CategoryTheory.SplitEpi.{u1, u3} C _inst_1 X Y f) -> (forall (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2), CategoryTheory.SplitEpi.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 F X Y f))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {X : C} {Y : C} {f : Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) X Y}, (CategoryTheory.SplitEpi.{u1, u3} C _inst_1 X Y f) -> (forall (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2), CategoryTheory.SplitEpi.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) Y) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) X Y f))
Case conversion may be inaccurate. Consider using '#align category_theory.split_epi.map CategoryTheory.SplitEpi.mapₓ'. -/
/-- Split epimorphisms are also absolute epimorphisms. -/
@[simps]
def SplitEpi.map {X Y : C} {f : X ⟶ Y} (se : SplitEpi f) (F : C ⥤ D) : SplitEpi (F.map f)
    where
  section_ := F.map se.section_
  id' := by rw [← functor.map_comp, split_epi.id, Functor.map_id]
#align category_theory.split_epi.map CategoryTheory.SplitEpi.map

instance {X Y : C} (f : X ⟶ Y) [hf : IsSplitMono f] (F : C ⥤ D) : IsSplitMono (F.map f) :=
  IsSplitMono.mk' (hf.exists_splitMono.some.map F)

instance {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] (F : C ⥤ D) : IsSplitEpi (F.map f) :=
  IsSplitEpi.mk' (hf.exists_splitEpi.some.map F)

end

end CategoryTheory

