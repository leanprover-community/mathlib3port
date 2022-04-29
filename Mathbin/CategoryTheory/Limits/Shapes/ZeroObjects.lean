/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin
-/
import Mathbin.CategoryTheory.Limits.Shapes.Products
import Mathbin.CategoryTheory.Limits.Shapes.Images
import Mathbin.CategoryTheory.IsomorphismClasses

/-!
# Zero objects

A category "has a zero object" if it has an object which is both initial and terminal. Having a
zero object provides zero morphisms, as the unique morphisms factoring through the zero object;
see `category_theory.limits.shapes.zero_morphisms`.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/


noncomputable section

universe v u v' u'

open CategoryTheory

open CategoryTheory.Category

variable {C : Type u} [Category.{v} C]

variable {D : Type u'} [Category.{v'} D]

namespace CategoryTheory

namespace Limits

/-- An object `X` in a category is a *zero object* if for every object `Y`
there is a unique morphism `to : X → Y` and a unique morphism `from : Y → X`.

This is a characteristic predicate for `has_zero_object`. -/
structure IsZero (X : C) : Prop where
  unique_to : ∀ Y, Nonempty (Unique (X ⟶ Y))
  unique_from : ∀ Y, Nonempty (Unique (Y ⟶ X))

namespace IsZero

variable {X Y : C}

/-- If `h : is_zero X`, then `h.to Y` is a choice of unique morphism `X → Y`. -/
protected def to (h : IsZero X) (Y : C) : X ⟶ Y :=
  @default (X ⟶ Y) <| @Unique.inhabited _ <| (h.unique_to Y).some

theorem eq_to (h : IsZero X) (f : X ⟶ Y) : f = h.to Y :=
  @Unique.eq_default _ (id _) _

theorem to_eq (h : IsZero X) (f : X ⟶ Y) : h.to Y = f :=
  (h.eq_to f).symm

/-- If `h : is_zero X`, then `h.from Y` is a choice of unique morphism `Y → X`. -/
protected def from (h : IsZero X) (Y : C) : Y ⟶ X :=
  @default (Y ⟶ X) <| @Unique.inhabited _ <| (h.unique_from Y).some

theorem eq_from (h : IsZero X) (f : Y ⟶ X) : f = h.from Y :=
  @Unique.eq_default _ (id _) _

theorem from_eq (h : IsZero X) (f : Y ⟶ X) : h.from Y = f :=
  (h.eq_from f).symm

theorem eq_of_src (hX : IsZero X) (f g : X ⟶ Y) : f = g :=
  (hX.eq_to f).trans (hX.eq_to g).symm

theorem eq_of_tgt (hX : IsZero X) (f g : Y ⟶ X) : f = g :=
  (hX.eq_from f).trans (hX.eq_from g).symm

/-- Any two zero objects are isomorphic. -/
def iso (hX : IsZero X) (hY : IsZero Y) : X ≅ Y where
  Hom := hX.to Y
  inv := hX.from Y
  hom_inv_id' := hX.eq_of_src _ _
  inv_hom_id' := hY.eq_of_src _ _

/-- A zero object is in particular initial. -/
protected def isInitial (hX : IsZero X) : IsInitial X :=
  (@IsInitial.ofUnique _ _ X) fun Y => (hX.unique_to Y).some

/-- A zero object is in particular terminal. -/
protected def isTerminal (hX : IsZero X) : IsTerminal X :=
  (@IsTerminal.ofUnique _ _ X) fun Y => (hX.unique_from Y).some

/-- The (unique) isomorphism between any initial object and the zero object. -/
def isoIsInitial (hX : IsZero X) (hY : IsInitial Y) : X ≅ Y :=
  hX.IsInitial.uniqueUpToIso hY

/-- The (unique) isomorphism between any terminal object and the zero object. -/
def isoIsTerminal (hX : IsZero X) (hY : IsTerminal Y) : X ≅ Y :=
  hX.IsTerminal.uniqueUpToIso hY

theorem of_iso (hY : IsZero Y) (e : X ≅ Y) : IsZero X := by
  refine' ⟨fun Z => ⟨⟨⟨e.hom ≫ hY.to Z⟩, fun f => _⟩⟩, fun Z => ⟨⟨⟨hY.from Z ≫ e.inv⟩, fun f => _⟩⟩⟩
  · rw [← cancel_epi e.inv]
    apply hY.eq_of_src
    
  · rw [← cancel_mono e.hom]
    apply hY.eq_of_tgt
    

end IsZero

end Limits

open CategoryTheory.Limits

theorem Iso.is_zero_iff {X Y : C} (e : X ≅ Y) : IsZero X ↔ IsZero Y :=
  ⟨fun h => h.of_iso e.symm, fun h => h.of_iso e⟩

theorem Functor.is_zero (F : C ⥤ D) (hF : ∀ X, IsZero (F.obj X)) : IsZero F := by
  constructor <;> intro G <;> refine' ⟨⟨⟨_⟩, _⟩⟩
  · refine' { app := fun X => (hF _).to _, naturality' := _ }
    intros
    exact (hF _).eq_of_src _ _
    
  · intro f
    ext
    apply (hF _).eq_of_src _ _
    
  · refine' { app := fun X => (hF _).from _, naturality' := _ }
    intros
    exact (hF _).eq_of_tgt _ _
    
  · intro f
    ext
    apply (hF _).eq_of_tgt _ _
    

namespace Limits

variable (C)

/-- A category "has a zero object" if it has an object which is both initial and terminal. -/
class HasZeroObject : Prop where
  zero : ∃ X : C, IsZero X

instance has_zero_object_punit : HasZeroObject (Discrete PUnit) where
  zero :=
    ⟨PUnit.unit, by
      tidy, by
      tidy⟩

section

variable [HasZeroObject C]

/-- Construct a `has_zero C` for a category with a zero object.
This can not be a global instance as it will trigger for every `has_zero C` typeclass search.
-/
protected def HasZeroObject.hasZero : Zero C where
  zero := HasZeroObject.zero.some

localized [ZeroObject] attribute [instance] CategoryTheory.Limits.HasZeroObject.hasZero

theorem is_zero_zero : IsZero (0 : C) :=
  HasZeroObject.zero.some_spec

end

open ZeroObject

variable {C}

theorem IsZero.has_zero_object {X : C} (hX : IsZero X) : HasZeroObject C :=
  ⟨⟨X, hX⟩⟩

/-- Every zero object is isomorphic to *the* zero object. -/
def IsZero.isoZero [HasZeroObject C] {X : C} (hX : IsZero X) : X ≅ 0 :=
  hX.Iso (is_zero_zero C)

theorem IsZero.obj [HasZeroObject D] {F : C ⥤ D} (hF : IsZero F) (X : C) : IsZero (F.obj X) := by
  let G : C ⥤ D := (CategoryTheory.Functor.const C).obj 0
  have hG : is_zero G := functor.is_zero _ fun X => is_zero_zero _
  let e : F ≅ G := hF.iso hG
  exact (is_zero_zero _).of_iso (e.app X)

namespace HasZeroObject

variable [HasZeroObject C]

/-- There is a unique morphism from the zero object to any object `X`. -/
protected def uniqueTo (X : C) : Unique (0 ⟶ X) :=
  ((is_zero_zero C).unique_to X).some

/-- There is a unique morphism from any object `X` to the zero object. -/
protected def uniqueFrom (X : C) : Unique (X ⟶ 0) :=
  ((is_zero_zero C).unique_from X).some

localized [ZeroObject] attribute [instance] CategoryTheory.Limits.HasZeroObject.uniqueTo

localized [ZeroObject] attribute [instance] CategoryTheory.Limits.HasZeroObject.uniqueFrom

@[ext]
theorem to_zero_ext {X : C} (f g : X ⟶ 0) : f = g :=
  (is_zero_zero C).eq_of_tgt _ _

@[ext]
theorem from_zero_ext {X : C} (f g : 0 ⟶ X) : f = g :=
  (is_zero_zero C).eq_of_src _ _

instance (X : C) : Subsingleton (X ≅ 0) := by
  tidy

instance {X : C} (f : 0 ⟶ X) : Mono f where
  right_cancellation := fun Z g h w => by
    ext

instance {X : C} (f : X ⟶ 0) : Epi f where
  left_cancellation := fun Z g h w => by
    ext

/-- A zero object is in particular initial. -/
def zeroIsInitial : IsInitial (0 : C) :=
  (is_zero_zero C).IsInitial

/-- A zero object is in particular terminal. -/
def zeroIsTerminal : IsTerminal (0 : C) :=
  (is_zero_zero C).IsTerminal

/-- A zero object is in particular initial. -/
instance (priority := 10) has_initial : HasInitial C :=
  has_initial_of_unique 0

/-- A zero object is in particular terminal. -/
instance (priority := 10) has_terminal : HasTerminal C :=
  has_terminal_of_unique 0

/-- The (unique) isomorphism between any initial object and the zero object. -/
def zeroIsoIsInitial {X : C} (t : IsInitial X) : 0 ≅ X :=
  zeroIsInitial.uniqueUpToIso t

/-- The (unique) isomorphism between any terminal object and the zero object. -/
def zeroIsoIsTerminal {X : C} (t : IsTerminal X) : 0 ≅ X :=
  zeroIsTerminal.uniqueUpToIso t

/-- The (unique) isomorphism between the chosen initial object and the chosen zero object. -/
def zeroIsoInitial [HasInitial C] : 0 ≅ ⊥_ C :=
  zeroIsInitial.uniqueUpToIso initialIsInitial

/-- The (unique) isomorphism between the chosen terminal object and the chosen zero object. -/
def zeroIsoTerminal [HasTerminal C] : 0 ≅ ⊤_ C :=
  zeroIsTerminal.uniqueUpToIso terminalIsTerminal

instance (priority := 100) has_strict_initial : InitialMonoClass C :=
  InitialMonoClass.of_is_initial zeroIsInitial fun X => CategoryTheory.mono _

end HasZeroObject

end Limits

open CategoryTheory.Limits

open ZeroObject

theorem Functor.is_zero_iff [HasZeroObject D] (F : C ⥤ D) : IsZero F ↔ ∀ X, IsZero (F.obj X) :=
  ⟨fun hF X => hF.obj X, Functor.is_zero _⟩

end CategoryTheory

