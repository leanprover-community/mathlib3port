/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Scott Morrison
-/
import Mathbin.CategoryTheory.Adjunction.Basic
import Mathbin.CategoryTheory.Opposites
import Mathbin.CategoryTheory.Groupoid

/-!
# Facts about epimorphisms and monomorphisms.

The definitions of `epi` and `mono` are in `category_theory.category`,
since they are used by some lemmas for `iso`, which is used everywhere.
-/


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

instance unop_mono_of_epi {A B : Cᵒᵖ} (f : A ⟶ B) [Epi f] : Mono f.unop :=
  ⟨fun Z g h eq => Quiver.Hom.op_inj ((cancel_epi f).1 (Quiver.Hom.unop_inj Eq))⟩

instance unop_epi_of_mono {A B : Cᵒᵖ} (f : A ⟶ B) [Mono f] : Epi f.unop :=
  ⟨fun Z g h eq => Quiver.Hom.op_inj ((cancel_mono f).1 (Quiver.Hom.unop_inj Eq))⟩

instance op_mono_of_epi {A B : C} (f : A ⟶ B) [Epi f] : Mono f.op :=
  ⟨fun Z g h eq => Quiver.Hom.unop_inj ((cancel_epi f).1 (Quiver.Hom.op_inj Eq))⟩

instance op_epi_of_mono {A B : C} (f : A ⟶ B) [Mono f] : Epi f.op :=
  ⟨fun Z g h eq => Quiver.Hom.unop_inj ((cancel_mono f).1 (Quiver.Hom.op_inj Eq))⟩

/-- A split monomorphism is a morphism `f : X ⟶ Y` with a given retraction `retraction f : Y ⟶ X`
such that `f ≫ retraction f = 𝟙 X`.

Every split monomorphism is a monomorphism.
-/
@[ext, nolint has_nonempty_instance]
structure SplitMono {X Y : C} (f : X ⟶ Y) where
  retraction : Y ⟶ X
  id' : f ≫ retraction = 𝟙 X := by
    run_tac
      obviously

restate_axiom split_mono.id'

attribute [simp, reassoc] split_mono.id

/-- `is_split_mono f` is the assertion that `f` admits a retraction -/
class IsSplitMono {X Y : C} (f : X ⟶ Y) : Prop where
  exists_split_mono : Nonempty (SplitMono f)

/-- A constructor for `is_split_mono f` taking a `split_mono f` as an argument -/
theorem IsSplitMono.mk' {X Y : C} {f : X ⟶ Y} (sm : SplitMono f) : IsSplitMono f :=
  ⟨Nonempty.intro sm⟩

/-- A split epimorphism is a morphism `f : X ⟶ Y` with a given section `section_ f : Y ⟶ X`
such that `section_ f ≫ f = 𝟙 Y`.
(Note that `section` is a reserved keyword, so we append an underscore.)

Every split epimorphism is an epimorphism.
-/
@[ext, nolint has_nonempty_instance]
structure SplitEpi {X Y : C} (f : X ⟶ Y) where
  section_ : Y ⟶ X
  id' : section_ ≫ f = 𝟙 Y := by
    run_tac
      obviously

restate_axiom split_epi.id'

attribute [simp, reassoc] split_epi.id

/-- `is_split_epi f` is the assertion that `f` admits a section -/
class IsSplitEpi {X Y : C} (f : X ⟶ Y) : Prop where
  exists_split_epi : Nonempty (SplitEpi f)

/-- A constructor for `is_split_epi f` taking a `split_epi f` as an argument -/
theorem IsSplitEpi.mk' {X Y : C} {f : X ⟶ Y} (se : SplitEpi f) : IsSplitEpi f :=
  ⟨Nonempty.intro se⟩

/-- The chosen retraction of a split monomorphism. -/
noncomputable def retraction {X Y : C} (f : X ⟶ Y) [hf : IsSplitMono f] : Y ⟶ X :=
  hf.exists_split_mono.some.retraction

@[simp, reassoc]
theorem IsSplitMono.id {X Y : C} (f : X ⟶ Y) [hf : IsSplitMono f] : f ≫ retraction f = 𝟙 X :=
  hf.exists_split_mono.some.id

/-- The retraction of a split monomorphism has an obvious section. -/
def SplitMono.splitEpi {X Y : C} {f : X ⟶ Y} (sm : SplitMono f) : SplitEpi sm.retraction where section_ := f

/-- The retraction of a split monomorphism is itself a split epimorphism. -/
instance retraction_is_split_epi {X Y : C} (f : X ⟶ Y) [hf : IsSplitMono f] : IsSplitEpi (retraction f) :=
  IsSplitEpi.mk' (SplitMono.splitEpi _)

/-- A split mono which is epi is an iso. -/
theorem is_iso_of_epi_of_is_split_mono {X Y : C} (f : X ⟶ Y) [IsSplitMono f] [Epi f] : IsIso f :=
  ⟨⟨retraction f,
      ⟨by
        simp , by
        simp [← cancel_epi f]⟩⟩⟩

/-- The chosen section of a split epimorphism.
(Note that `section` is a reserved keyword, so we append an underscore.)
-/
noncomputable def section_ {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] : Y ⟶ X :=
  hf.exists_split_epi.some.section_

@[simp, reassoc]
theorem IsSplitEpi.id {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] : section_ f ≫ f = 𝟙 Y :=
  hf.exists_split_epi.some.id

/-- The section of a split epimorphism has an obvious retraction. -/
def SplitEpi.splitMono {X Y : C} {f : X ⟶ Y} (se : SplitEpi f) : SplitMono se.section_ where retraction := f

/-- The section of a split epimorphism is itself a split monomorphism. -/
instance section_is_split_mono {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] : IsSplitMono (section_ f) :=
  IsSplitMono.mk' (SplitEpi.splitMono _)

/-- A split epi which is mono is an iso. -/
theorem is_iso_of_mono_of_is_split_epi {X Y : C} (f : X ⟶ Y) [Mono f] [IsSplitEpi f] : IsIso f :=
  ⟨⟨section_ f,
      ⟨by
        simp [← cancel_mono f], by
        simp ⟩⟩⟩

/-- Every iso is a split mono. -/
instance (priority := 100) IsSplitMono.of_iso {X Y : C} (f : X ⟶ Y) [IsIso f] : IsSplitMono f :=
  IsSplitMono.mk' { retraction := inv f }

/-- Every iso is a split epi. -/
instance (priority := 100) IsSplitEpi.of_iso {X Y : C} (f : X ⟶ Y) [IsIso f] : IsSplitEpi f :=
  IsSplitEpi.mk' { section_ := inv f }

theorem SplitMono.mono {X Y : C} {f : X ⟶ Y} (sm : SplitMono f) : Mono f :=
  { right_cancellation := fun Z g h w => by
      replace w := w =≫ sm.retraction
      simpa using w }

/-- Every split mono is a mono. -/
instance (priority := 100) IsSplitMono.mono {X Y : C} (f : X ⟶ Y) [hf : IsSplitMono f] : Mono f :=
  hf.exists_split_mono.some.mono

theorem SplitEpi.epi {X Y : C} {f : X ⟶ Y} (se : SplitEpi f) : Epi f :=
  { left_cancellation := fun Z g h w => by
      replace w := se.section_ ≫= w
      simpa using w }

/-- Every split epi is an epi. -/
instance (priority := 100) IsSplitEpi.epi {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] : Epi f :=
  hf.exists_split_epi.some.Epi

/-- Every split mono whose retraction is mono is an iso. -/
theorem IsIso.of_mono_retraction' {X Y : C} {f : X ⟶ Y} (hf : SplitMono f) [mono <| hf.retraction] : IsIso f :=
  ⟨⟨hf.retraction,
      ⟨by
        simp ,
        (cancel_mono_id <| hf.retraction).mp
          (by
            simp )⟩⟩⟩

/-- Every split mono whose retraction is mono is an iso. -/
theorem IsIso.of_mono_retraction {X Y : C} (f : X ⟶ Y) [hf : IsSplitMono f] [hf' : mono <| retraction f] : IsIso f :=
  @IsIso.of_mono_retraction' _ _ _ _ _ hf.exists_split_mono.some hf'

/-- Every split epi whose section is epi is an iso. -/
theorem IsIso.of_epi_section' {X Y : C} {f : X ⟶ Y} (hf : SplitEpi f) [epi <| hf.section_] : IsIso f :=
  ⟨⟨hf.section_,
      ⟨(cancel_epi_id <| hf.section_).mp
          (by
            simp ),
        by
        simp ⟩⟩⟩

/-- Every split epi whose section is epi is an iso. -/
theorem IsIso.of_epi_section {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] [hf' : epi <| section_ f] : IsIso f :=
  @IsIso.of_epi_section' _ _ _ _ _ hf.exists_split_epi.some hf'

-- FIXME this has unnecessarily become noncomputable!
/-- A category where every morphism has a `trunc` retraction is computably a groupoid. -/
noncomputable def Groupoid.ofTruncSplitMono (all_split_mono : ∀ {X Y : C} (f : X ⟶ Y), Trunc (IsSplitMono f)) :
    Groupoid.{v₁} C := by
  apply groupoid.of_is_iso
  intro X Y f
  trunc_cases all_split_mono f
  trunc_cases all_split_mono (retraction f)
  apply is_iso.of_mono_retraction

section

variable (C)

/-- A split mono category is a category in which every monomorphism is split. -/
class SplitMonoCategory where
  is_split_mono_of_mono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], IsSplitMono f

/-- A split epi category is a category in which every epimorphism is split. -/
class SplitEpiCategory where
  is_split_epi_of_epi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], IsSplitEpi f

end

/-- In a category in which every monomorphism is split, every monomorphism splits. This is not an
    instance because it would create an instance loop. -/
theorem is_split_mono_of_mono [SplitMonoCategory C] {X Y : C} (f : X ⟶ Y) [Mono f] : IsSplitMono f :=
  SplitMonoCategory.is_split_mono_of_mono _

/-- In a category in which every epimorphism is split, every epimorphism splits. This is not an
    instance because it would create an instance loop. -/
theorem is_split_epi_of_epi [SplitEpiCategory C] {X Y : C} (f : X ⟶ Y) [Epi f] : IsSplitEpi f :=
  SplitEpiCategory.is_split_epi_of_epi _

section

variable {D : Type u₂} [Category.{v₂} D]

/-- Split monomorphisms are also absolute monomorphisms. -/
@[simps]
def SplitMono.map {X Y : C} {f : X ⟶ Y} (sm : SplitMono f) (F : C ⥤ D) : SplitMono (F.map f) where
  retraction := F.map sm.retraction
  id' := by
    rw [← functor.map_comp, split_mono.id, Functor.map_id]

/-- Split epimorphisms are also absolute epimorphisms. -/
@[simps]
def SplitEpi.map {X Y : C} {f : X ⟶ Y} (se : SplitEpi f) (F : C ⥤ D) : SplitEpi (F.map f) where
  section_ := F.map se.section_
  id' := by
    rw [← functor.map_comp, split_epi.id, Functor.map_id]

instance {X Y : C} (f : X ⟶ Y) [hf : IsSplitMono f] (F : C ⥤ D) : IsSplitMono (F.map f) :=
  IsSplitMono.mk' (hf.exists_split_mono.some.map F)

instance {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] (F : C ⥤ D) : IsSplitEpi (F.map f) :=
  IsSplitEpi.mk' (hf.exists_split_epi.some.map F)

end

end CategoryTheory

