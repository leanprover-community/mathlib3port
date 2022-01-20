import Mathbin.CategoryTheory.Limits.HasLimits
import Mathbin.CategoryTheory.Thin

/-!
# Wide pullbacks

We define the category `wide_pullback_shape`, (resp. `wide_pushout_shape`) which is the category
obtained from a discrete category of type `J` by adjoining a terminal (resp. initial) element.
Limits of this shape are wide pullbacks (pushouts).
The convenience method `wide_cospan` (`wide_span`) constructs a functor from this category, hitting
the given morphisms.

We use `wide_pullback_shape` to define ordinary pullbacks (pushouts) by using `J := walking_pair`,
which allows easy proofs of some related lemmas.
Furthermore, wide pullbacks are used to show the existence of limits in the slice category.
Namely, if `C` has wide pullbacks then `C/B` has limits for any object `B` in `C`.

Typeclasses `has_wide_pullbacks` and `has_finite_wide_pullbacks` assert the existence of wide
pullbacks and finite wide pullbacks.
-/


universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

variable (J : Type v)

/-- A wide pullback shape for any type `J` can be written simply as `option J`. -/
def wide_pullback_shape :=
  Option J deriving Inhabited

/-- A wide pushout shape for any type `J` can be written simply as `option J`. -/
def wide_pushout_shape :=
  Option J deriving Inhabited

namespace WidePullbackShape

variable {J}

/-- The type of arrows for the shape indexing a wide pullback. -/
inductive hom : wide_pullback_shape J → wide_pullback_shape J → Type v
  | id : ∀ X, hom X X
  | term : ∀ j : J, hom (some j) none
  deriving DecidableEq

attribute [nolint unused_arguments] hom.decidable_eq

instance struct : category_struct (wide_pullback_shape J) where
  Hom := hom
  id := fun j => hom.id j
  comp := fun j₁ j₂ j₃ f g => by
    cases f
    exact g
    cases g
    apply hom.term _

instance hom.inhabited : Inhabited (hom none none) :=
  ⟨hom.id (none : wide_pullback_shape J)⟩

attribute [local tidy] tactic.case_bash

instance subsingleton_hom (j j' : wide_pullback_shape J) : Subsingleton (j ⟶ j') :=
  ⟨by
    tidy⟩

instance category : small_category (wide_pullback_shape J) :=
  thin_category

@[simp]
theorem hom_id (X : wide_pullback_shape J) : hom.id X = 𝟙 X :=
  rfl

variable {C : Type u} [category.{v} C]

/-- Construct a functor out of the wide pullback shape given a J-indexed collection of arrows to a
fixed object.
-/
@[simps]
def wide_cospan (B : C) (objs : J → C) (arrows : ∀ j : J, objs j ⟶ B) : wide_pullback_shape J ⥤ C where
  obj := fun j => Option.casesOn j B objs
  map := fun X Y f => by
    cases' f with _ j
    · apply 𝟙 _
      
    · exact arrows j
      
  map_comp' := fun _ _ _ f g => by
    cases f
    · simpa
      
    cases g
    simp

/-- Every diagram is naturally isomorphic (actually, equal) to a `wide_cospan` -/
def diagram_iso_wide_cospan (F : wide_pullback_shape J ⥤ C) :
    F ≅ wide_cospan (F.obj none) (fun j => F.obj (some j)) fun j => F.map (hom.term j) :=
  (nat_iso.of_components fun j =>
      eq_to_iso $ by
        tidy) $
    by
    tidy

/-- Construct a cone over a wide cospan. -/
@[simps]
def mk_cone {F : wide_pullback_shape J ⥤ C} {X : C} (f : X ⟶ F.obj none) (π : ∀ j, X ⟶ F.obj (some j))
    (w : ∀ j, π j ≫ F.map (hom.term j) = f) : cone F :=
  { x,
    π :=
      { app := fun j =>
          match j with
          | none => f
          | some j => π j,
        naturality' := fun j j' f => by
          cases j <;> cases j' <;> cases f <;> unfold_aux <;> dsimp <;> simp [w] } }

end WidePullbackShape

namespace WidePushoutShape

variable {J}

/-- The type of arrows for the shape indexing a wide psuhout. -/
inductive hom : wide_pushout_shape J → wide_pushout_shape J → Type v
  | id : ∀ X, hom X X
  | init : ∀ j : J, hom none (some j)
  deriving DecidableEq

attribute [nolint unused_arguments] hom.decidable_eq

instance struct : category_struct (wide_pushout_shape J) where
  Hom := hom
  id := fun j => hom.id j
  comp := fun j₁ j₂ j₃ f g => by
    cases f
    exact g
    cases g
    apply hom.init _

instance hom.inhabited : Inhabited (hom none none) :=
  ⟨hom.id (none : wide_pushout_shape J)⟩

attribute [local tidy] tactic.case_bash

instance subsingleton_hom (j j' : wide_pushout_shape J) : Subsingleton (j ⟶ j') :=
  ⟨by
    tidy⟩

instance category : small_category (wide_pushout_shape J) :=
  thin_category

@[simp]
theorem hom_id (X : wide_pushout_shape J) : hom.id X = 𝟙 X :=
  rfl

variable {C : Type u} [category.{v} C]

/-- Construct a functor out of the wide pushout shape given a J-indexed collection of arrows from a
fixed object.
-/
@[simps]
def wide_span (B : C) (objs : J → C) (arrows : ∀ j : J, B ⟶ objs j) : wide_pushout_shape J ⥤ C where
  obj := fun j => Option.casesOn j B objs
  map := fun X Y f => by
    cases' f with _ j
    · apply 𝟙 _
      
    · exact arrows j
      
  map_comp' := by
    rintro (_ | _) (_ | _) (_ | _) (_ | _) (_ | _) <;>
      first |
        simpa|
        simp

/-- Every diagram is naturally isomorphic (actually, equal) to a `wide_span` -/
def diagram_iso_wide_span (F : wide_pushout_shape J ⥤ C) :
    F ≅ wide_span (F.obj none) (fun j => F.obj (some j)) fun j => F.map (hom.init j) :=
  (nat_iso.of_components fun j =>
      eq_to_iso $ by
        tidy) $
    by
    tidy

/-- Construct a cocone over a wide span. -/
@[simps]
def mk_cocone {F : wide_pushout_shape J ⥤ C} {X : C} (f : F.obj none ⟶ X) (ι : ∀ j, F.obj (some j) ⟶ X)
    (w : ∀ j, F.map (hom.init j) ≫ ι j = f) : cocone F :=
  { x,
    ι :=
      { app := fun j =>
          match j with
          | none => f
          | some j => ι j,
        naturality' := fun j j' f => by
          cases j <;> cases j' <;> cases f <;> unfold_aux <;> dsimp <;> simp [w] } }

end WidePushoutShape

variable (C : Type u) [category.{v} C]

/-- `has_wide_pullbacks` represents a choice of wide pullback for every collection of morphisms -/
abbrev has_wide_pullbacks : Prop :=
  ∀ J : Type v, has_limits_of_shape (wide_pullback_shape J) C

/-- `has_wide_pushouts` represents a choice of wide pushout for every collection of morphisms -/
abbrev has_wide_pushouts : Prop :=
  ∀ J : Type v, has_colimits_of_shape (wide_pushout_shape J) C

variable {C J}

/-- `has_wide_pullback B objs arrows` means that `wide_cospan B objs arrows` has a limit. -/
abbrev has_wide_pullback (B : C) (objs : J → C) (arrows : ∀ j : J, objs j ⟶ B) : Prop :=
  has_limit (wide_pullback_shape.wide_cospan B objs arrows)

/-- `has_wide_pushout B objs arrows` means that `wide_span B objs arrows` has a colimit. -/
abbrev has_wide_pushout (B : C) (objs : J → C) (arrows : ∀ j : J, B ⟶ objs j) : Prop :=
  has_colimit (wide_pushout_shape.wide_span B objs arrows)

/-- A choice of wide pullback. -/
noncomputable abbrev wide_pullback (B : C) (objs : J → C) (arrows : ∀ j : J, objs j ⟶ B)
    [has_wide_pullback B objs arrows] : C :=
  limit (wide_pullback_shape.wide_cospan B objs arrows)

/-- A choice of wide pushout. -/
noncomputable abbrev wide_pushout (B : C) (objs : J → C) (arrows : ∀ j : J, B ⟶ objs j)
    [has_wide_pushout B objs arrows] : C :=
  colimit (wide_pushout_shape.wide_span B objs arrows)

variable (C)

namespace WidePullback

variable {C} {B : C} {objs : J → C} (arrows : ∀ j : J, objs j ⟶ B)

variable [has_wide_pullback B objs arrows]

/-- The `j`-th projection from the pullback. -/
noncomputable abbrev π (j : J) : wide_pullback _ _ arrows ⟶ objs j :=
  limit.π (wide_pullback_shape.wide_cospan _ _ _) (Option.some j)

/-- The unique map to the base from the pullback. -/
noncomputable abbrev base : wide_pullback _ _ arrows ⟶ B :=
  limit.π (wide_pullback_shape.wide_cospan _ _ _) Option.none

@[simp, reassoc]
theorem π_arrow (j : J) : π arrows j ≫ arrows _ = base arrows := by
  apply limit.w (wide_pullback_shape.wide_cospan _ _ _) (wide_pullback_shape.hom.term j)

variable {arrows}

/-- Lift a collection of morphisms to a morphism to the pullback. -/
noncomputable abbrev lift {X : C} (f : X ⟶ B) (fs : ∀ j : J, X ⟶ objs j) (w : ∀ j, fs j ≫ arrows j = f) :
    X ⟶ wide_pullback _ _ arrows :=
  limit.lift (wide_pullback_shape.wide_cospan _ _ _) (wide_pullback_shape.mk_cone f fs $ w)

variable (arrows)

variable {X : C} (f : X ⟶ B) (fs : ∀ j : J, X ⟶ objs j) (w : ∀ j, fs j ≫ arrows j = f)

@[simp, reassoc]
theorem lift_π (j : J) : lift f fs w ≫ π arrows j = fs _ := by
  simp
  rfl

@[simp, reassoc]
theorem liftBase : lift f fs w ≫ base arrows = f := by
  simp
  rfl

theorem eq_lift_of_comp_eq (g : X ⟶ wide_pullback _ _ arrows) :
    (∀ j : J, g ≫ π arrows j = fs j) → g ≫ base arrows = f → g = lift f fs w := by
  intro h1 h2
  apply (limit.is_limit (wide_pullback_shape.wide_cospan B objs arrows)).uniq (wide_pullback_shape.mk_cone f fs $ w)
  rintro (_ | _)
  · apply h2
    
  · apply h1
    

theorem hom_eq_lift (g : X ⟶ wide_pullback _ _ arrows) :
    g =
      lift (g ≫ base arrows) (fun j => g ≫ π arrows j)
        (by
          tidy) :=
  by
  apply eq_lift_of_comp_eq
  tidy

@[ext]
theorem hom_ext (g1 g2 : X ⟶ wide_pullback _ _ arrows) :
    (∀ j : J, g1 ≫ π arrows j = g2 ≫ π arrows j) → g1 ≫ base arrows = g2 ≫ base arrows → g1 = g2 := by
  intro h1 h2
  apply limit.hom_ext
  rintro (_ | _)
  · apply h2
    
  · apply h1
    

end WidePullback

namespace WidePushout

variable {C} {B : C} {objs : J → C} (arrows : ∀ j : J, B ⟶ objs j)

variable [has_wide_pushout B objs arrows]

/-- The `j`-th inclusion to the pushout. -/
noncomputable abbrev ι (j : J) : objs j ⟶ wide_pushout _ _ arrows :=
  colimit.ι (wide_pushout_shape.wide_span _ _ _) (Option.some j)

/-- The unique map from the head to the pushout. -/
noncomputable abbrev head : B ⟶ wide_pushout B objs arrows :=
  colimit.ι (wide_pushout_shape.wide_span _ _ _) Option.none

@[simp, reassoc]
theorem arrow_ι (j : J) : arrows j ≫ ι arrows j = head arrows := by
  apply colimit.w (wide_pushout_shape.wide_span _ _ _) (wide_pushout_shape.hom.init j)

variable {arrows}

/-- Descend a collection of morphisms to a morphism from the pushout. -/
noncomputable abbrev desc {X : C} (f : B ⟶ X) (fs : ∀ j : J, objs j ⟶ X) (w : ∀ j, arrows j ≫ fs j = f) :
    wide_pushout _ _ arrows ⟶ X :=
  colimit.desc (wide_pushout_shape.wide_span B objs arrows) (wide_pushout_shape.mk_cocone f fs $ w)

variable (arrows)

variable {X : C} (f : B ⟶ X) (fs : ∀ j : J, objs j ⟶ X) (w : ∀ j, arrows j ≫ fs j = f)

@[simp, reassoc]
theorem ι_desc (j : J) : ι arrows j ≫ desc f fs w = fs _ := by
  simp
  rfl

@[simp, reassoc]
theorem head_desc : head arrows ≫ desc f fs w = f := by
  simp
  rfl

theorem eq_desc_of_comp_eq (g : wide_pushout _ _ arrows ⟶ X) :
    (∀ j : J, ι arrows j ≫ g = fs j) → head arrows ≫ g = f → g = desc f fs w := by
  intro h1 h2
  apply (colimit.is_colimit (wide_pushout_shape.wide_span B objs arrows)).uniq (wide_pushout_shape.mk_cocone f fs $ w)
  rintro (_ | _)
  · apply h2
    
  · apply h1
    

theorem hom_eq_desc (g : wide_pushout _ _ arrows ⟶ X) :
    g =
      desc (head arrows ≫ g) (fun j => ι arrows j ≫ g) fun j => by
        rw [← category.assoc]
        simp :=
  by
  apply eq_desc_of_comp_eq
  tidy

@[ext]
theorem hom_ext (g1 g2 : wide_pushout _ _ arrows ⟶ X) :
    (∀ j : J, ι arrows j ≫ g1 = ι arrows j ≫ g2) → head arrows ≫ g1 = head arrows ≫ g2 → g1 = g2 := by
  intro h1 h2
  apply colimit.hom_ext
  rintro (_ | _)
  · apply h2
    
  · apply h1
    

end WidePushout

end CategoryTheory.Limits

