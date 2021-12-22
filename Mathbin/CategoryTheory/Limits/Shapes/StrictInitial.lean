import Mathbin.CategoryTheory.Limits.Shapes.Terminal
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.EpiMono

/-!
# Strict initial objects

This file sets up the basic theory of strict initial objects: initial objects where every morphism
to it is an isomorphism. This generalises a property of the empty set in the category of sets:
namely that the only function to the empty set is from itself.

We say `C` has strict initial objects if every initial object is strict, ie given any morphism
`f : A ⟶ I` where `I` is initial, then `f` is an isomorphism.
Strictly speaking, this says that *any* initial object must be strict, rather than that strict
initial objects exist, which turns out to be a more useful notion to formalise.

If the binary product of `X` with a strict initial object exists, it is also initial.

To show a category `C` with an initial object has strict initial objects, the most convenient way
is to show any morphism to the (chosen) initial object is an isomorphism and use
`has_strict_initial_objects_of_initial_is_strict`.

The dual notion (strict terminal objects) occurs much less frequently in practice so is ignored.

## TODO

* Construct examples of this: `Type*`, `Top`, `Groupoid`, simplicial types, posets.
* Construct the bottom element of the subobject lattice given strict initials.
* Show cartesian closed categories have strict initials

## References
* https://ncatlab.org/nlab/show/strict+initial+object
-/


universe v u

namespace CategoryTheory

namespace Limits

open Category

variable (C : Type u) [category.{v} C]

section StrictInitial

/-- 
We say `C` has strict initial objects if every initial object is strict, ie given any morphism
`f : A ⟶ I` where `I` is initial, then `f` is an isomorphism.

Strictly speaking, this says that *any* initial object must be strict, rather than that strict
initial objects exist.
-/
class has_strict_initial_objects : Prop where
  out : ∀ {I A : C} f : A ⟶ I, is_initial I → is_iso f

variable {C}

section

variable [has_strict_initial_objects C] {I : C}

theorem is_initial.is_iso_to (hI : is_initial I) {A : C} (f : A ⟶ I) : is_iso f :=
  has_strict_initial_objects.out f hI

theorem is_initial.strict_hom_ext (hI : is_initial I) {A : C} (f g : A ⟶ I) : f = g := by
  have := hI.is_iso_to f
  have := hI.is_iso_to g
  exact eq_of_inv_eq_inv (hI.hom_ext (inv f) (inv g))

theorem is_initial.subsingleton_to (hI : is_initial I) {A : C} : Subsingleton (A ⟶ I) :=
  ⟨hI.strict_hom_ext⟩

-- failed to format: format: uncaught backtrack exception
instance
  ( priority := 100 )
  initial_mono_of_strict_initial_objects
  : initial_mono_class C
  where is_initial_mono_from I A hI := { right_cancellation := fun B g h i => hI.strict_hom_ext _ _ }

/--  If `I` is initial, then `X ⨯ I` is isomorphic to it. -/
@[simps Hom]
noncomputable def mul_is_initial (X : C) [has_binary_product X I] (hI : is_initial I) : X ⨯ I ≅ I :=
  @as_iso _ Prod.snd (hI.is_iso_to _)

@[simp]
theorem mul_is_initial_inv (X : C) [has_binary_product X I] (hI : is_initial I) : (mul_is_initial X hI).inv = hI.to _ :=
  hI.hom_ext _ _

/--  If `I` is initial, then `I ⨯ X` is isomorphic to it. -/
@[simps Hom]
noncomputable def is_initial_mul (X : C) [has_binary_product I X] (hI : is_initial I) : I ⨯ X ≅ I :=
  @as_iso _ Prod.fst (hI.is_iso_to _)

@[simp]
theorem is_initial_mul_inv (X : C) [has_binary_product I X] (hI : is_initial I) : (is_initial_mul X hI).inv = hI.to _ :=
  hI.hom_ext _ _

variable [has_initial C]

instance initial_is_iso_to {A : C} (f : A ⟶ ⊥_ C) : is_iso f :=
  initial_is_initial.is_iso_to _

@[ext]
theorem initial.hom_ext {A : C} (f g : A ⟶ ⊥_ C) : f = g :=
  initial_is_initial.strict_hom_ext _ _

theorem initial.subsingleton_to {A : C} : Subsingleton (A ⟶ ⊥_ C) :=
  initial_is_initial.subsingleton_to

/-- 
The product of `X` with an initial object in a category with strict initial objects is itself
initial.
This is the generalisation of the fact that `X × empty ≃ empty` for types (or `n * 0 = 0`).
-/
@[simps Hom]
noncomputable def mul_initial (X : C) [has_binary_product X (⊥_ C)] : X ⨯ ⊥_ C ≅ ⊥_ C :=
  mul_is_initial _ initial_is_initial

@[simp]
theorem mul_initial_inv (X : C) [has_binary_product X (⊥_ C)] : (mul_initial X).inv = initial.to _ :=
  Subsingleton.elimₓ _ _

/-- 
The product of `X` with an initial object in a category with strict initial objects is itself
initial.
This is the generalisation of the fact that `empty × X ≃ empty` for types (or `0 * n = 0`).
-/
@[simps Hom]
noncomputable def initial_mul (X : C) [has_binary_product (⊥_ C) X] : (⊥_ C) ⨯ X ≅ ⊥_ C :=
  is_initial_mul _ initial_is_initial

@[simp]
theorem initial_mul_inv (X : C) [has_binary_product (⊥_ C) X] : (initial_mul X).inv = initial.to _ :=
  Subsingleton.elimₓ _ _

end

/--  If `C` has an initial object such that every morphism *to* it is an isomorphism, then `C`
has strict initial objects. -/
theorem has_strict_initial_objects_of_initial_is_strict [has_initial C] (h : ∀ A f : A ⟶ ⊥_ C, is_iso f) :
    has_strict_initial_objects C :=
  { out := fun I A f hI => by
      have := h A (f ≫ hI.to _)
      exact
        ⟨⟨hI.to _ ≫ inv (f ≫ hI.to (⊥_ C)), by
            rw [← assoc, is_iso.hom_inv_id], hI.hom_ext _ _⟩⟩ }

end StrictInitial

section StrictTerminal

/-- 
We say `C` has strict terminal objects if every terminal object is strict, ie given any morphism
`f : I ⟶ A` where `I` is terminal, then `f` is an isomorphism.

Strictly speaking, this says that *any* terminal object must be strict, rather than that strict
terminal objects exist.
-/
class has_strict_terminal_objects : Prop where
  out : ∀ {I A : C} f : I ⟶ A, is_terminal I → is_iso f

variable {C}

section

variable [has_strict_terminal_objects C] {I : C}

theorem is_terminal.is_iso_from (hI : is_terminal I) {A : C} (f : I ⟶ A) : is_iso f :=
  has_strict_terminal_objects.out f hI

theorem is_terminal.strict_hom_ext (hI : is_terminal I) {A : C} (f g : I ⟶ A) : f = g := by
  have := hI.is_iso_from f
  have := hI.is_iso_from g
  exact eq_of_inv_eq_inv (hI.hom_ext (inv f) (inv g))

theorem is_terminal.subsingleton_to (hI : is_terminal I) {A : C} : Subsingleton (I ⟶ A) :=
  ⟨hI.strict_hom_ext⟩

variable {J : Type v} [small_category J]

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (j «expr ≠ » i)
/--  If all but one object in a diagram is strict terminal, the the limit is isomorphic to the
said object via `limit.π`. -/
theorem limit_π_is_iso_of_is_strict_terminal (F : J ⥤ C) [has_limit F] (i : J)
    (H : ∀ j _ : j ≠ i, is_terminal (F.obj j)) [Subsingleton (i ⟶ i)] : is_iso (limit.π F i) := by
  classical
  refine' ⟨⟨limit.lift _ ⟨_, ⟨_, _⟩⟩, _, _⟩⟩
  ·
    exact fun j =>
      dite (j = i)
        (fun h =>
          eq_to_hom
            (by
              cases h
              rfl))
        fun h => (H _ h).from _
  ·
    intro j k f
    split_ifs
    ·
      cases h
      cases h_1
      have : f = 𝟙 _ := Subsingleton.elimₓ _ _
      subst this
      simpa
    ·
      cases h
      erw [category.comp_id]
      have : is_iso (F.map f) := (H _ h_1).is_iso_from _
      rw [← is_iso.comp_inv_eq]
      apply (H _ h_1).hom_ext
    ·
      cases h_1
      apply (H _ h).hom_ext
    ·
      apply (H _ h).hom_ext
  ·
    ext
    rw [assoc, limit.lift_π]
    dsimp only
    split_ifs
    ·
      cases h
      rw [id_comp, eq_to_hom_refl]
      exact comp_id _
    ·
      apply (H _ h).hom_ext
  ·
    rw [limit.lift_π]
    simpa

variable [has_terminal C]

instance terminal_is_iso_from {A : C} (f : ⊤_ C ⟶ A) : is_iso f :=
  terminal_is_terminal.is_iso_from _

@[ext]
theorem terminal.hom_ext {A : C} (f g : ⊤_ C ⟶ A) : f = g :=
  terminal_is_terminal.strict_hom_ext _ _

theorem terminal.subsingleton_to {A : C} : Subsingleton (⊤_ C ⟶ A) :=
  terminal_is_terminal.subsingleton_to

end

/--  If `C` has an object such that every morphism *from* it is an isomorphism, then `C`
has strict terminal objects. -/
theorem has_strict_terminal_objects_of_terminal_is_strict (I : C) (h : ∀ A f : I ⟶ A, is_iso f) :
    has_strict_terminal_objects C :=
  { out := fun I' A f hI' => by
      have := h A (hI'.from _ ≫ f)
      exact
        ⟨⟨inv (hI'.from I ≫ f) ≫ hI'.from I, hI'.hom_ext _ _, by
            rw [assoc, is_iso.inv_hom_id]⟩⟩ }

end StrictTerminal

end Limits

end CategoryTheory

