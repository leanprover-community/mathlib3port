/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathbin.CategoryTheory.Balanced
import Mathbin.CategoryTheory.LiftingProperties.Basic

/-!
# Strong epimorphisms

In this file, we define strong epimorphisms. A strong epimorphism is an epimorphism `f`
which has the (unique) left lifting property with respect to monomorphisms. Similarly,
a strong monomorphisms in a monomorphism which has the (unique) right lifting property
with respect to epimorphisms.

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

/-- A strong epimorphism `f` is an epimorphism which has the left lifting property
with respect to monomorphisms. -/
class StrongEpi (f : P ⟶ Q) : Prop where
  Epi : Epi f
  llp : ∀ ⦃X Y : C⦄ (z : X ⟶ Y) [Mono z], HasLiftingProperty f z

theorem StrongEpi.mk' {f : P ⟶ Q} [Epi f]
    (hf : ∀ (X Y : C) (z : X ⟶ Y) (hz : Mono z) (u : P ⟶ X) (v : Q ⟶ Y) (sq : CommSq u f z v), sq.HasLift) :
    StrongEpi f :=
  { Epi := inferInstance, llp := fun X Y z hz => ⟨fun u v sq => hf X Y z hz u v sq⟩ }

/-- A strong monomorphism `f` is a monomorphism which has the right lifting property
with respect to epimorphisms. -/
class StrongMono (f : P ⟶ Q) : Prop where
  mono : Mono f
  rlp : ∀ ⦃X Y : C⦄ (z : X ⟶ Y) [Epi z], HasLiftingProperty z f

theorem StrongMono.mk' {f : P ⟶ Q} [Mono f]
    (hf : ∀ (X Y : C) (z : X ⟶ Y) (hz : Epi z) (u : X ⟶ P) (v : Y ⟶ Q) (sq : CommSq u z f v), sq.HasLift) :
    StrongMono f :=
  { mono := inferInstance, rlp := fun X Y z hz => ⟨fun u v sq => hf X Y z hz u v sq⟩ }

attribute [instance] strong_epi.llp

attribute [instance] strong_mono.rlp

instance (priority := 100) epi_of_strong_epi (f : P ⟶ Q) [StrongEpi f] : Epi f :=
  strong_epi.epi

instance (priority := 100) mono_of_strong_mono (f : P ⟶ Q) [StrongMono f] : Mono f :=
  strong_mono.mono

section

variable {R : C} (f : P ⟶ Q) (g : Q ⟶ R)

/-- The composition of two strong epimorphisms is a strong epimorphism. -/
theorem strong_epi_comp [StrongEpi f] [StrongEpi g] : StrongEpi (f ≫ g) :=
  { Epi := epi_comp _ _,
    llp := by
      intros
      infer_instance }

/-- The composition of two strong monomorphisms is a strong monomorphism. -/
theorem strong_mono_comp [StrongMono f] [StrongMono g] : StrongMono (f ≫ g) :=
  { mono := mono_comp _ _,
    rlp := by
      intros
      infer_instance }

/-- If `f ≫ g` is a strong epimorphism, then so is `g`. -/
theorem strong_epi_of_strong_epi [StrongEpi (f ≫ g)] : StrongEpi g :=
  { Epi := epi_of_epi f g,
    llp := by
      intros
      constructor
      intro u v sq
      have h₀ : (f ≫ u) ≫ z = (f ≫ g) ≫ v := by
        simp only [category.assoc, sq.w]
      exact
        comm_sq.has_lift.mk'
          ⟨(comm_sq.mk h₀).lift, by
            simp only [← cancel_mono z, category.assoc, comm_sq.fac_right, sq.w], by
            simp ⟩ }

/-- If `f ≫ g` is a strong monomorphism, then so is `f`. -/
theorem strong_mono_of_strong_mono [StrongMono (f ≫ g)] : StrongMono f :=
  { mono := mono_of_mono f g,
    rlp := by
      intros
      constructor
      intro u v sq
      have h₀ : u ≫ f ≫ g = z ≫ v ≫ g := by
        rw [reassoc_of sq.w]
      exact
        comm_sq.has_lift.mk'
          ⟨(comm_sq.mk h₀).lift, by
            simp , by
            simp [← cancel_epi z, sq.w]⟩ }

/-- An isomorphism is in particular a strong epimorphism. -/
instance (priority := 100) strong_epi_of_is_iso [IsIso f] : StrongEpi f where
  Epi := by
    infer_instance
  llp := fun X Y z hz => HasLiftingProperty.of_left_iso _ _

/-- An isomorphism is in particular a strong monomorphism. -/
instance (priority := 100) strong_mono_of_is_iso [IsIso f] : StrongMono f where
  mono := by
    infer_instance
  rlp := fun X Y z hz => HasLiftingProperty.of_right_iso _ _

end

/-- A strong epimorphism that is a monomorphism is an isomorphism. -/
theorem is_iso_of_mono_of_strong_epi (f : P ⟶ Q) [Mono f] [StrongEpi f] : IsIso f :=
  ⟨⟨(CommSq.mk
          (show 𝟙 P ≫ f = f ≫ 𝟙 Q by
            simp )).lift,
      by
      tidy⟩⟩

/-- A strong monomorphism that is an epimorphism is an isomorphism. -/
theorem is_iso_of_epi_of_strong_mono (f : P ⟶ Q) [Epi f] [StrongMono f] : IsIso f :=
  ⟨⟨(CommSq.mk
          (show 𝟙 P ≫ f = f ≫ 𝟙 Q by
            simp )).lift,
      by
      tidy⟩⟩

section

variable (C)

/-- A strong epi category is a category in which every epimorphism is strong. -/
class StrongEpiCategory : Prop where
  strong_epi_of_epi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], StrongEpi f

/-- A strong mono category is a category in which every monomorphism is strong. -/
class StrongMonoCategory : Prop where
  strong_mono_of_mono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], StrongMono f

end

theorem strong_epi_of_epi [StrongEpiCategory C] (f : P ⟶ Q) [Epi f] : StrongEpi f :=
  StrongEpiCategory.strong_epi_of_epi _

theorem strong_mono_of_mono [StrongMonoCategory C] (f : P ⟶ Q) [Mono f] : StrongMono f :=
  StrongMonoCategory.strong_mono_of_mono _

section

attribute [local instance] strong_epi_of_epi

instance (priority := 100) balanced_of_strong_epi_category [StrongEpiCategory C] :
    Balanced C where is_iso_of_mono_of_epi := fun _ _ _ _ _ => is_iso_of_mono_of_strong_epi _

end

section

attribute [local instance] strong_mono_of_mono

instance (priority := 100) balanced_of_strong_mono_category [StrongMonoCategory C] :
    Balanced C where is_iso_of_mono_of_epi := fun _ _ _ _ _ => is_iso_of_epi_of_strong_mono _

end

end CategoryTheory

