/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathbin.CategoryTheory.Arrow
import Mathbin.CategoryTheory.Balanced

/-!
# Strong epimorphisms

In this file, we define strong epimorphisms. A strong epimorphism is an epimorphism `f`, such
that for every commutative square with `f` at the top and a monomorphism at the bottom, there is
a diagonal morphism making the two triangles commute. This lift is necessarily unique (as shown in
`comma.lean`).

## Main results

Besides the definition, we show that
* the composition of two strong epimorphisms is a strong epimorphism,
* if `f ≫ g` is a strong epimorphism, then so is `g`,
* if `f` is both a strong epimorphism and a monomorphism, then it is an isomorphism

We also define classes `strong_mono_category` and `strong_epi_category` for categories in which
every monomorphism or epimorphism is strong, and deduce that these categories are balanced.

## TODO

Show that the dual of a strong epimorphism is a strong monomorphism, and vice versa.

## References

* [F. Borceux, *Handbook of Categorical Algebra 1*][borceux-vol1]
-/


universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

variable {P Q : C}

/-- A strong epimorphism `f` is an epimorphism such that every commutative square with `f` at the
    top and a monomorphism at the bottom has a lift. -/
class StrongEpi (f : P ⟶ Q) : Prop where
  Epi : Epi f
  HasLift : ∀ {X Y : C} {u : P ⟶ X} {v : Q ⟶ Y} {z : X ⟶ Y} [Mono z] h : u ≫ z = f ≫ v, arrow.has_lift <| Arrow.homMk' h

/-- A strong monomorphism `f` is a monomorphism such that every commutative square with `f` at the
    bottom and an epimorphism at the top has a lift. -/
class StrongMono (f : P ⟶ Q) : Prop where
  mono : Mono f
  HasLift : ∀ {X Y : C} {u : X ⟶ P} {v : Y ⟶ Q} {z : X ⟶ Y} [Epi z] h : u ≫ f = z ≫ v, arrow.has_lift <| Arrow.homMk' h

attribute [instance] strong_epi.has_lift

attribute [instance] strong_mono.has_lift

instance (priority := 100) epi_of_strong_epi (f : P ⟶ Q) [StrongEpi f] : Epi f :=
  strong_epi.epi

instance (priority := 100) mono_of_strong_mono (f : P ⟶ Q) [StrongMono f] : Mono f :=
  strong_mono.mono

section

variable {R : C} (f : P ⟶ Q) (g : Q ⟶ R)

/-- The composition of two strong epimorphisms is a strong epimorphism. -/
theorem strong_epi_comp [StrongEpi f] [StrongEpi g] : StrongEpi (f ≫ g) :=
  { Epi := epi_comp _ _,
    HasLift := by
      intros
      have h₀ : u ≫ z = f ≫ g ≫ v := by
        simpa [category.assoc] using h
      let w : Q ⟶ X := arrow.lift (arrow.hom_mk' h₀)
      have h₁ : w ≫ z = g ≫ v := by
        rw [arrow.lift_mk'_right]
      exact
        arrow.has_lift.mk
          ⟨(arrow.lift (arrow.hom_mk' h₁) : R ⟶ X), by
            simp , by
            simp ⟩ }

/-- The composition of two strong monomorphisms is a strong monomorphism. -/
theorem strong_mono_comp [StrongMono f] [StrongMono g] : StrongMono (f ≫ g) :=
  { mono := mono_comp _ _,
    HasLift := by
      intros
      have h₀ : (u ≫ f) ≫ g = z ≫ v := by
        simpa [category.assoc] using h
      let w : Y ⟶ Q := arrow.lift (arrow.hom_mk' h₀)
      have h₁ : u ≫ f = z ≫ w := by
        rw [arrow.lift_mk'_left]
      exact
        arrow.has_lift.mk
          ⟨(arrow.lift (arrow.hom_mk' h₁) : Y ⟶ P), by
            simp , by
            simp ⟩ }

/-- If `f ≫ g` is a strong epimorphism, then so is `g`. -/
theorem strong_epi_of_strong_epi [StrongEpi (f ≫ g)] : StrongEpi g :=
  { Epi := epi_of_epi f g,
    HasLift := by
      intros
      have h₀ : (f ≫ u) ≫ z = (f ≫ g) ≫ v := by
        simp only [category.assoc, h]
      exact
        arrow.has_lift.mk
          ⟨(arrow.lift (arrow.hom_mk' h₀) : R ⟶ X),
            (cancel_mono z).1
              (by
                simp [h]),
            by
            simp ⟩ }

/-- If `f ≫ g` is a strong monomorphism, then so is `f`. -/
theorem strong_mono_of_strong_mono [StrongMono (f ≫ g)] : StrongMono f :=
  { mono := mono_of_mono f g,
    HasLift := by
      intros
      have h₀ : u ≫ f ≫ g = z ≫ v ≫ g := by
        rw [reassoc_of h]
      exact
        arrow.has_lift.mk
          ⟨(arrow.lift (arrow.hom_mk' h₀) : Y ⟶ P), by
            simp ,
            (cancel_epi z).1
              (by
                simp [h])⟩ }

/-- An isomorphism is in particular a strong epimorphism. -/
instance (priority := 100) strong_epi_of_is_iso [IsIso f] : StrongEpi f where
  Epi := by
    infer_instance
  HasLift := fun X Y u v z _ h =>
    Arrow.HasLift.mk
      ⟨inv f ≫ u, by
        simp , by
        simp [h]⟩

/-- An isomorphism is in particular a strong monomorphism. -/
instance (priority := 100) strong_mono_of_is_iso [IsIso f] : StrongMono f where
  mono := by
    infer_instance
  HasLift := fun X Y u v z _ h =>
    Arrow.HasLift.mk
      ⟨v ≫ inv f, by
        simp [← category.assoc, ← h], by
        simp ⟩

end

/-- A strong epimorphism that is a monomorphism is an isomorphism. -/
theorem is_iso_of_mono_of_strong_epi (f : P ⟶ Q) [Mono f] [StrongEpi f] : IsIso f :=
  ⟨⟨arrow.lift <|
        arrow.hom_mk' <|
          show 𝟙 P ≫ f = f ≫ 𝟙 Q by
            simp ,
      by
      tidy⟩⟩

/-- A strong monomorphism that is an epimorphism is an isomorphism. -/
theorem is_iso_of_epi_of_strong_mono (f : P ⟶ Q) [Epi f] [StrongMono f] : IsIso f :=
  ⟨⟨arrow.lift <|
        arrow.hom_mk' <|
          show 𝟙 P ≫ f = f ≫ 𝟙 Q by
            simp ,
      by
      tidy⟩⟩

section

variable (C)

/-- A strong epi category is a category in which every epimorphism is strong. -/
class StrongEpiCategory : Prop where
  strong_epi_of_epi : ∀ {X Y : C} f : X ⟶ Y [Epi f], StrongEpi f

/-- A strong mono category is a category in which every monomorphism is strong. -/
class StrongMonoCategory : Prop where
  strong_mono_of_mono : ∀ {X Y : C} f : X ⟶ Y [Mono f], StrongMono f

end

theorem strong_epi_of_epi [StrongEpiCategory C] (f : P ⟶ Q) [Epi f] : StrongEpi f :=
  StrongEpiCategory.strong_epi_of_epi _

theorem strong_mono_of_mono [StrongMonoCategory C] (f : P ⟶ Q) [Mono f] : StrongMono f :=
  StrongMonoCategory.strong_mono_of_mono _

section

attribute [local instance] strong_epi_of_epi

instance (priority := 100) balanced_of_strong_epi_category [StrongEpiCategory C] : Balanced C where
  is_iso_of_mono_of_epi := fun _ _ _ _ _ => is_iso_of_mono_of_strong_epi _

end

section

attribute [local instance] strong_mono_of_mono

instance (priority := 100) balanced_of_strong_mono_category [StrongMonoCategory C] : Balanced C where
  is_iso_of_mono_of_epi := fun _ _ _ _ _ => is_iso_of_epi_of_strong_mono _

end

end CategoryTheory

