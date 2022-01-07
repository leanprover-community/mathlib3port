import Mathbin.CategoryTheory.Limits.Shapes.Terminal

/-!

# `with_initial` and `with_terminal`

Given a category `C`, this file constructs two objects:
1. `with_terminal C`, the category built from `C` by formally adjoining a terminal object.
2. `with_initial C`, the category built from `C` by formally adjoining an initial object.

The terminal resp. initial object is `with_terminal.star` resp. `with_initial.star`, and
the proofs that these are terminal resp. initial are in `with_terminal.star_terminal`
and `with_initial.star_initial`.

The inclusion from `C` intro `with_terminal C` resp. `with_initial C` is denoted
`with_terminal.incl` resp. `with_initial.incl`.

The relevant constructions needed for the universal properties of these constructions are:
1. `lift`, which lifts `F : C ⥤ D` to a functor from `with_terminal C` resp. `with_initial C` in
  the case where an object `Z : D` is provided satisfying some additional conditions.
2. `incl_lift` shows that the composition of `lift` with `incl` is isomorphic to the
  functor which was lifted.
3. `lift_unique` provides the uniqueness property of `lift`.

In addition to this, we provide `with_terminal.map` and `with_initinal.map` providing the
functoriality of these constructions with respect to functors on the base categories.

-/


namespace CategoryTheory

universe v u

variable (C : Type u) [category.{v} C]

/-- Formally adjoin a terminal object to a category. -/
inductive with_terminal : Type u
  | of : C → with_terminal
  | star : with_terminal
  deriving Inhabited

/-- Formally adjoin an initial object to a category. -/
inductive with_initial : Type u
  | of : C → with_initial
  | star : with_initial
  deriving Inhabited

namespace WithTerminal

attribute [local tidy] tactic.case_bash

variable {C}

/-- Morphisms for `with_terminal C`. -/
@[simp, nolint has_inhabited_instance]
def hom : with_terminal C → with_terminal C → Type v
  | of X, of Y => X ⟶ Y
  | star, of X => Pempty
  | _, star => PUnit

/-- Identity morphisms for `with_terminal C`. -/
@[simp]
def id : ∀ X : with_terminal C, hom X X
  | of X => 𝟙 _
  | star => PUnit.unit

/-- Composition of morphisms for `with_terminal C`. -/
@[simp]
def comp : ∀ {X Y Z : with_terminal C}, hom X Y → hom Y Z → hom X Z
  | of X, of Y, of Z => fun f g => f ≫ g
  | of X, _, star => fun f g => PUnit.unit
  | star, of X, _ => fun f g => Pempty.elimₓ f
  | _, star, of Y => fun f g => Pempty.elimₓ g
  | star, star, star => fun _ _ => PUnit.unit

instance : category.{v} (with_terminal C) where
  Hom := fun X Y => hom X Y
  id := fun X => id _
  comp := fun X Y Z f g => comp f g

/-- The inclusion from `C` into `with_terminal C`. -/
def incl : C ⥤ with_terminal C where
  obj := of
  map := fun X Y f => f

instance : full (incl : C ⥤ _) where
  Preimage := fun X Y f => f

instance : faithful (incl : C ⥤ _) :=
  {  }

/-- Map `with_terminal` with respect to a functor `F : C ⥤ D`. -/
def map {D : Type _} [category D] (F : C ⥤ D) : with_terminal C ⥤ with_terminal D where
  obj := fun X =>
    match X with
    | of x => of $ F.obj x
    | star => star
  map := fun X Y f =>
    match X, Y, f with
    | of x, of y, f => F.map f
    | of x, star, PUnit.unit => PUnit.unit
    | star, star, PUnit.unit => PUnit.unit

instance {X : with_terminal C} : Unique (X ⟶ star) where
  default :=
    match X with
    | of x => PUnit.unit
    | star => PUnit.unit
  uniq := by
    tidy

/-- `with_terminal.star` is terminal. -/
def star_terminal : limits.is_terminal (star : with_terminal C) :=
  limits.is_terminal.of_unique _

/-- Lift a functor `F : C ⥤ D` to `with_term C ⥤ D`. -/
@[simps]
def lift {D : Type _} [category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ x y : C f : x ⟶ y, F.map f ≫ M y = M x) : with_terminal C ⥤ D where
  obj := fun X =>
    match X with
    | of x => F.obj x
    | star => Z
  map := fun X Y f =>
    match X, Y, f with
    | of x, of y, f => F.map f
    | of x, star, PUnit.unit => M x
    | star, star, PUnit.unit => 𝟙 Z

/-- The isomorphism between `incl ⋙ lift F _ _` with `F`. -/
@[simps]
def incl_lift {D : Type _} [category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ x y : C f : x ⟶ y, F.map f ≫ M y = M x) : incl ⋙ lift F M hM ≅ F where
  Hom := { app := fun X => 𝟙 _ }
  inv := { app := fun X => 𝟙 _ }

/-- The isomorphism between `(lift F _ _).obj with_terminal.star` with `Z`. -/
@[simps]
def lift_star {D : Type _} [category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ x y : C f : x ⟶ y, F.map f ≫ M y = M x) : (lift F M hM).obj star ≅ Z :=
  eq_to_iso rfl

theorem lift_map_lift_star {D : Type _} [category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ x y : C f : x ⟶ y, F.map f ≫ M y = M x) (x : C) :
    (lift F M hM).map (star_terminal.from (incl.obj x)) ≫ (lift_star F M hM).Hom = (incl_lift F M hM).Hom.app x ≫ M x :=
  by
  erw [category.id_comp, category.comp_id]
  rfl

/-- The uniqueness of `lift`. -/
@[simp]
def lift_unique {D : Type _} [category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ x y : C f : x ⟶ y, F.map f ≫ M y = M x) (G : with_terminal C ⥤ D) (h : incl ⋙ G ≅ F) (hG : G.obj star ≅ Z)
    (hh : ∀ x : C, G.map (star_terminal.from (incl.obj x)) ≫ hG.hom = h.hom.app x ≫ M x) : G ≅ lift F M hM :=
  nat_iso.of_components
    (fun X =>
      match X with
      | of x => h.app x
      | star => hG)
    (by
      rintro (X | X) (Y | Y) f
      · apply h.hom.naturality
        
      · cases f
        exact hh _
        
      · cases f
        
      · cases f
        change G.map (𝟙 _) ≫ hG.hom = hG.hom ≫ 𝟙 _
        simp
        )

/-- A variant of `lift` with `Z` a terminal object. -/
@[simps]
def lift_to_terminal {D : Type _} [category D] {Z : D} (F : C ⥤ D) (hZ : limits.is_terminal Z) : with_terminal C ⥤ D :=
  lift F (fun x => hZ.from _) fun x y f => hZ.hom_ext _ _

/-- A variant of `incl_lift` with `Z` a terminal object. -/
@[simps]
def incl_lift_to_terminal {D : Type _} [category D] {Z : D} (F : C ⥤ D) (hZ : limits.is_terminal Z) :
    incl ⋙ lift_to_terminal F hZ ≅ F :=
  incl_lift _ _ _

/-- A variant of `lift_unique` with `Z` a terminal object. -/
@[simps]
def lift_to_terminal_unique {D : Type _} [category D] {Z : D} (F : C ⥤ D) (hZ : limits.is_terminal Z)
    (G : with_terminal C ⥤ D) (h : incl ⋙ G ≅ F) (hG : G.obj star ≅ Z) : G ≅ lift_to_terminal F hZ :=
  lift_unique F (fun z => hZ.from _) (fun x y f => hZ.hom_ext _ _) G h hG fun x => hZ.hom_ext _ _

/-- Constructs a morphism to `star` from `of X`. -/
@[simp]
def hom_from (X : C) : incl.obj X ⟶ star :=
  star_terminal.from _

instance is_iso_of_from_star {X : with_terminal C} (f : star ⟶ X) : is_iso f := by
  tidy

end WithTerminal

namespace WithInitial

attribute [local tidy] tactic.case_bash

variable {C}

/-- Morphisms for `with_initial C`. -/
@[simp, nolint has_inhabited_instance]
def hom : with_initial C → with_initial C → Type v
  | of X, of Y => X ⟶ Y
  | of X, _ => Pempty
  | star, _ => PUnit

/-- Identity morphisms for `with_initial C`. -/
@[simp]
def id : ∀ X : with_initial C, hom X X
  | of X => 𝟙 _
  | star => PUnit.unit

/-- Composition of morphisms for `with_initial C`. -/
@[simp]
def comp : ∀ {X Y Z : with_initial C}, hom X Y → hom Y Z → hom X Z
  | of X, of Y, of Z => fun f g => f ≫ g
  | star, _, of X => fun f g => PUnit.unit
  | _, of X, star => fun f g => Pempty.elimₓ g
  | of Y, star, _ => fun f g => Pempty.elimₓ f
  | star, star, star => fun _ _ => PUnit.unit

instance : category.{v} (with_initial C) where
  Hom := fun X Y => hom X Y
  id := fun X => id _
  comp := fun X Y Z f g => comp f g

/-- The inclusion of `C` into `with_initial C`. -/
def incl : C ⥤ with_initial C where
  obj := of
  map := fun X Y f => f

instance : full (incl : C ⥤ _) where
  Preimage := fun X Y f => f

instance : faithful (incl : C ⥤ _) :=
  {  }

/-- Map `with_initial` with respect to a functor `F : C ⥤ D`. -/
def map {D : Type _} [category D] (F : C ⥤ D) : with_initial C ⥤ with_initial D where
  obj := fun X =>
    match X with
    | of x => of $ F.obj x
    | star => star
  map := fun X Y f =>
    match X, Y, f with
    | of x, of y, f => F.map f
    | star, of x, PUnit.unit => PUnit.unit
    | star, star, PUnit.unit => PUnit.unit

instance {X : with_initial C} : Unique (star ⟶ X) where
  default :=
    match X with
    | of x => PUnit.unit
    | star => PUnit.unit
  uniq := by
    tidy

/-- `with_initial.star` is initial. -/
def star_initial : limits.is_initial (star : with_initial C) :=
  limits.is_initial.of_unique _

/-- Lift a functor `F : C ⥤ D` to `with_initial C ⥤ D`. -/
@[simps]
def lift {D : Type _} [category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ x y : C f : x ⟶ y, M x ≫ F.map f = M y) : with_initial C ⥤ D where
  obj := fun X =>
    match X with
    | of x => F.obj x
    | star => Z
  map := fun X Y f =>
    match X, Y, f with
    | of x, of y, f => F.map f
    | star, of x, PUnit.unit => M _
    | star, star, PUnit.unit => 𝟙 _

/-- The isomorphism between `incl ⋙ lift F _ _` with `F`. -/
@[simps]
def incl_lift {D : Type _} [category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ x y : C f : x ⟶ y, M x ≫ F.map f = M y) : incl ⋙ lift F M hM ≅ F where
  Hom := { app := fun X => 𝟙 _ }
  inv := { app := fun X => 𝟙 _ }

/-- The isomorphism between `(lift F _ _).obj with_term.star` with `Z`. -/
@[simps]
def lift_star {D : Type _} [category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ x y : C f : x ⟶ y, M x ≫ F.map f = M y) : (lift F M hM).obj star ≅ Z :=
  eq_to_iso rfl

theorem lift_star_lift_map {D : Type _} [category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ x y : C f : x ⟶ y, M x ≫ F.map f = M y) (x : C) :
    (lift_star F M hM).Hom ≫ (lift F M hM).map (star_initial.to (incl.obj x)) = M x ≫ (incl_lift F M hM).Hom.app x := by
  erw [category.id_comp, category.comp_id]
  rfl

/-- The uniqueness of `lift`. -/
@[simp]
def lift_unique {D : Type _} [category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ x y : C f : x ⟶ y, M x ≫ F.map f = M y) (G : with_initial C ⥤ D) (h : incl ⋙ G ≅ F) (hG : G.obj star ≅ Z)
    (hh : ∀ x : C, hG.symm.hom ≫ G.map (star_initial.to (incl.obj x)) = M x ≫ h.symm.hom.app x) : G ≅ lift F M hM :=
  nat_iso.of_components
    (fun X =>
      match X with
      | of x => h.app x
      | star => hG)
    (by
      rintro (X | X) (Y | Y) f
      · apply h.hom.naturality
        
      · cases f
        
      · cases f
        change G.map _ ≫ h.hom.app _ = hG.hom ≫ _
        symm
        erw [← iso.eq_inv_comp, ← category.assoc, hh]
        simpa
        
      · cases f
        change G.map (𝟙 _) ≫ hG.hom = hG.hom ≫ 𝟙 _
        simp
        )

/-- A variant of `lift` with `Z` an initial object. -/
@[simps]
def lift_to_initial {D : Type _} [category D] {Z : D} (F : C ⥤ D) (hZ : limits.is_initial Z) : with_initial C ⥤ D :=
  lift F (fun x => hZ.to _) fun x y f => hZ.hom_ext _ _

/-- A variant of `incl_lift` with `Z` an initial object. -/
@[simps]
def incl_lift_to_initial {D : Type _} [category D] {Z : D} (F : C ⥤ D) (hZ : limits.is_initial Z) :
    incl ⋙ lift_to_initial F hZ ≅ F :=
  incl_lift _ _ _

/-- A variant of `lift_unique` with `Z` an initial object. -/
@[simps]
def lift_to_initial_unique {D : Type _} [category D] {Z : D} (F : C ⥤ D) (hZ : limits.is_initial Z)
    (G : with_initial C ⥤ D) (h : incl ⋙ G ≅ F) (hG : G.obj star ≅ Z) : G ≅ lift_to_initial F hZ :=
  lift_unique F (fun z => hZ.to _) (fun x y f => hZ.hom_ext _ _) G h hG fun x => hZ.hom_ext _ _

/-- Constructs a morphism from `star` to `of X`. -/
@[simp]
def hom_to (X : C) : star ⟶ incl.obj X :=
  star_initial.to _

instance is_iso_of_to_star {X : with_initial C} (f : X ⟶ star) : is_iso f := by
  tidy

end WithInitial

end CategoryTheory

