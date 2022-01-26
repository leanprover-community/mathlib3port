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

variable {C : Type u₁} [category.{v₁} C]

instance unop_mono_of_epi {A B : Cᵒᵖ} (f : A ⟶ B) [epi f] : mono f.unop :=
  ⟨fun Z g h eq => Quiver.Hom.op_inj ((cancel_epi f).1 (Quiver.Hom.unop_inj Eq))⟩

instance unop_epi_of_mono {A B : Cᵒᵖ} (f : A ⟶ B) [mono f] : epi f.unop :=
  ⟨fun Z g h eq => Quiver.Hom.op_inj ((cancel_mono f).1 (Quiver.Hom.unop_inj Eq))⟩

instance op_mono_of_epi {A B : C} (f : A ⟶ B) [epi f] : mono f.op :=
  ⟨fun Z g h eq => Quiver.Hom.unop_inj ((cancel_epi f).1 (Quiver.Hom.op_inj Eq))⟩

instance op_epi_of_mono {A B : C} (f : A ⟶ B) [mono f] : epi f.op :=
  ⟨fun Z g h eq => Quiver.Hom.unop_inj ((cancel_mono f).1 (Quiver.Hom.op_inj Eq))⟩

section

variable {D : Type u₂} [category.{v₂} D]

theorem left_adjoint_preserves_epi {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {X Y : C} {f : X ⟶ Y} (hf : epi f) :
    epi (F.map f) := by
  constructor
  intro Z g h H
  replace H := congr_argₓ (adj.hom_equiv X Z) H
  rwa [adj.hom_equiv_naturality_left, adj.hom_equiv_naturality_left, cancel_epi, Equivₓ.apply_eq_iff_eq] at H

theorem right_adjoint_preserves_mono {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {X Y : D} {f : X ⟶ Y} (hf : mono f) :
    mono (G.map f) := by
  constructor
  intro Z g h H
  replace H := congr_argₓ (adj.hom_equiv Z Y).symm H
  rwa [adj.hom_equiv_naturality_right_symm, adj.hom_equiv_naturality_right_symm, cancel_mono, Equivₓ.apply_eq_iff_eq] at
    H

instance is_equivalence.epi_map {F : C ⥤ D} [is_left_adjoint F] {X Y : C} {f : X ⟶ Y} [h : epi f] : epi (F.map f) :=
  left_adjoint_preserves_epi (adjunction.of_left_adjoint F) h

instance is_equivalence.mono_map {F : C ⥤ D} [is_right_adjoint F] {X Y : C} {f : X ⟶ Y} [h : mono f] : mono (F.map f) :=
  right_adjoint_preserves_mono (adjunction.of_right_adjoint F) h

theorem faithful_reflects_epi (F : C ⥤ D) [faithful F] {X Y : C} {f : X ⟶ Y} (hf : epi (F.map f)) : epi f :=
  ⟨fun Z g h H =>
    F.map_injective <| by
      rw [← cancel_epi (F.map f), ← F.map_comp, ← F.map_comp, H]⟩

theorem faithful_reflects_mono (F : C ⥤ D) [faithful F] {X Y : C} {f : X ⟶ Y} (hf : mono (F.map f)) : mono f :=
  ⟨fun Z g h H =>
    F.map_injective <| by
      rw [← cancel_mono (F.map f), ← F.map_comp, ← F.map_comp, H]⟩

end

/-- A split monomorphism is a morphism `f : X ⟶ Y` admitting a retraction `retraction f : Y ⟶ X`
such that `f ≫ retraction f = 𝟙 X`.

Every split monomorphism is a monomorphism.
-/
class split_mono {X Y : C} (f : X ⟶ Y) where
  retraction : Y ⟶ X
  id' : f ≫ retraction = 𝟙 X := by
    run_tac
      obviously

/-- A split epimorphism is a morphism `f : X ⟶ Y` admitting a section `section_ f : Y ⟶ X`
such that `section_ f ≫ f = 𝟙 Y`.
(Note that `section` is a reserved keyword, so we append an underscore.)

Every split epimorphism is an epimorphism.
-/
class split_epi {X Y : C} (f : X ⟶ Y) where
  section_ : Y ⟶ X
  id' : section_ ≫ f = 𝟙 Y := by
    run_tac
      obviously

/-- The chosen retraction of a split monomorphism. -/
def retraction {X Y : C} (f : X ⟶ Y) [split_mono f] : Y ⟶ X :=
  split_mono.retraction f

@[simp, reassoc]
theorem split_mono.id {X Y : C} (f : X ⟶ Y) [split_mono f] : f ≫ retraction f = 𝟙 X :=
  split_mono.id'

/-- The retraction of a split monomorphism is itself a split epimorphism. -/
instance retraction_split_epi {X Y : C} (f : X ⟶ Y) [split_mono f] : split_epi (retraction f) where
  section_ := f

/-- A split mono which is epi is an iso. -/
theorem is_iso_of_epi_of_split_mono {X Y : C} (f : X ⟶ Y) [split_mono f] [epi f] : is_iso f :=
  ⟨⟨retraction f,
      ⟨by
        simp , by
        simp [← cancel_epi f]⟩⟩⟩

/-- The chosen section of a split epimorphism.
(Note that `section` is a reserved keyword, so we append an underscore.)
-/
def section_ {X Y : C} (f : X ⟶ Y) [split_epi f] : Y ⟶ X :=
  split_epi.section_ f

@[simp, reassoc]
theorem split_epi.id {X Y : C} (f : X ⟶ Y) [split_epi f] : section_ f ≫ f = 𝟙 Y :=
  split_epi.id'

/-- The section of a split epimorphism is itself a split monomorphism. -/
instance section_split_mono {X Y : C} (f : X ⟶ Y) [split_epi f] : split_mono (section_ f) where
  retraction := f

/-- A split epi which is mono is an iso. -/
theorem is_iso_of_mono_of_split_epi {X Y : C} (f : X ⟶ Y) [mono f] [split_epi f] : is_iso f :=
  ⟨⟨section_ f,
      ⟨by
        simp [← cancel_mono f], by
        simp ⟩⟩⟩

/-- Every iso is a split mono. -/
noncomputable instance (priority := 100) split_mono.of_iso {X Y : C} (f : X ⟶ Y) [is_iso f] : split_mono f where
  retraction := inv f

/-- Every iso is a split epi. -/
noncomputable instance (priority := 100) split_epi.of_iso {X Y : C} (f : X ⟶ Y) [is_iso f] : split_epi f where
  section_ := inv f

/-- Every split mono is a mono. -/
instance (priority := 100) split_mono.mono {X Y : C} (f : X ⟶ Y) [split_mono f] : mono f where
  right_cancellation := fun Z g h w => by
    replace w := w =≫ retraction f
    simpa using w

/-- Every split epi is an epi. -/
instance (priority := 100) split_epi.epi {X Y : C} (f : X ⟶ Y) [split_epi f] : epi f where
  left_cancellation := fun Z g h w => by
    replace w := section_ f ≫= w
    simpa using w

/-- Every split mono whose retraction is mono is an iso. -/
theorem is_iso.of_mono_retraction {X Y : C} {f : X ⟶ Y} [split_mono f] [mono <| retraction f] : is_iso f :=
  ⟨⟨retraction f,
      ⟨by
        simp ,
        (cancel_mono_id <| retraction f).mp
          (by
            simp )⟩⟩⟩

/-- Every split epi whose section is epi is an iso. -/
theorem is_iso.of_epi_section {X Y : C} {f : X ⟶ Y} [split_epi f] [epi <| section_ f] : is_iso f :=
  ⟨⟨section_ f,
      ⟨(cancel_epi_id <| section_ f).mp
          (by
            simp ),
        by
        simp ⟩⟩⟩

/-- A category where every morphism has a `trunc` retraction is computably a groupoid. -/
noncomputable def groupoid.of_trunc_split_mono (all_split_mono : ∀ {X Y : C} f : X ⟶ Y, Trunc (split_mono f)) :
    groupoid.{v₁} C := by
  apply groupoid.of_is_iso
  intro X Y f
  trunc_cases all_split_mono f
  trunc_cases all_split_mono (retraction f)
  apply is_iso.of_mono_retraction

section

variable {D : Type u₂} [category.{v₂} D]

/-- Split monomorphisms are also absolute monomorphisms. -/
instance {X Y : C} (f : X ⟶ Y) [split_mono f] (F : C ⥤ D) : split_mono (F.map f) where
  retraction := F.map (retraction f)
  id' := by
    rw [← functor.map_comp, split_mono.id, Functor.map_id]

/-- Split epimorphisms are also absolute epimorphisms. -/
instance {X Y : C} (f : X ⟶ Y) [split_epi f] (F : C ⥤ D) : split_epi (F.map f) where
  section_ := F.map (section_ f)
  id' := by
    rw [← functor.map_comp, split_epi.id, Functor.map_id]

end

end CategoryTheory

