/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.limits.shapes.terminal
! leanprover-community/mathlib commit 46a64b5b4268c594af770c44d9e502afc6a515cb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Pempty
import Mathbin.CategoryTheory.Limits.HasLimits
import Mathbin.CategoryTheory.EpiMono
import Mathbin.CategoryTheory.Category.Preorder

/-!
# Initial and terminal objects in a category.

## References
* [Stacks: Initial and final objects](https://stacks.math.columbia.edu/tag/002B)
-/


noncomputable section

universe w w' v v₁ v₂ u u₁ u₂

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

attribute [local tidy] tactic.discrete_cases

/-- Construct a cone for the empty diagram given an object. -/
@[simps]
def asEmptyCone (X : C) : Cone (Functor.empty.{0} C) :=
  { x
    π := by tidy }
#align category_theory.limits.as_empty_cone CategoryTheory.Limits.asEmptyCone

/-- Construct a cocone for the empty diagram given an object. -/
@[simps]
def asEmptyCocone (X : C) : Cocone (Functor.empty.{0} C) :=
  { x
    ι := by tidy }
#align category_theory.limits.as_empty_cocone CategoryTheory.Limits.asEmptyCocone

/-- `X` is terminal if the cone it induces on the empty diagram is limiting. -/
abbrev IsTerminal (X : C) :=
  IsLimit (asEmptyCone X)
#align category_theory.limits.is_terminal CategoryTheory.Limits.IsTerminal

/-- `X` is initial if the cocone it induces on the empty diagram is colimiting. -/
abbrev IsInitial (X : C) :=
  IsColimit (asEmptyCocone X)
#align category_theory.limits.is_initial CategoryTheory.Limits.IsInitial

/-- An object `Y` is terminal iff for every `X` there is a unique morphism `X ⟶ Y`. -/
def isTerminalEquivUnique (F : Discrete.{0} PEmpty.{1} ⥤ C) (Y : C) :
    IsLimit (⟨Y, by tidy⟩ : Cone F) ≃ ∀ X : C, Unique (X ⟶ Y)
    where
  toFun t X :=
    { default := t.lift ⟨X, by tidy⟩
      uniq := fun f => t.uniq ⟨X, by tidy⟩ f (by tidy) }
  invFun u :=
    { lift := fun s => (u s.x).default
      uniq' := fun s _ _ => (u s.x).2 _ }
  left_inv := by tidy
  right_inv := by tidy
#align category_theory.limits.is_terminal_equiv_unique CategoryTheory.Limits.isTerminalEquivUnique

/-- An object `Y` is terminal if for every `X` there is a unique morphism `X ⟶ Y`
    (as an instance). -/
def IsTerminal.ofUnique (Y : C) [h : ∀ X : C, Unique (X ⟶ Y)] : IsTerminal Y
    where lift s := (h s.x).default
#align category_theory.limits.is_terminal.of_unique CategoryTheory.Limits.IsTerminal.ofUnique

/-- If `α` is a preorder with top, then `⊤` is a terminal object. -/
def isTerminalTop {α : Type _} [Preorder α] [OrderTop α] : IsTerminal (⊤ : α) :=
  IsTerminal.ofUnique _
#align category_theory.limits.is_terminal_top CategoryTheory.Limits.isTerminalTop

/-- Transport a term of type `is_terminal` across an isomorphism. -/
def IsTerminal.ofIso {Y Z : C} (hY : IsTerminal Y) (i : Y ≅ Z) : IsTerminal Z :=
  IsLimit.ofIsoLimit hY
    { Hom := { Hom := i.Hom }
      inv := { Hom := i.inv } }
#align category_theory.limits.is_terminal.of_iso CategoryTheory.Limits.IsTerminal.ofIso

/-- An object `X` is initial iff for every `Y` there is a unique morphism `X ⟶ Y`. -/
def isInitialEquivUnique (F : Discrete.{0} PEmpty.{1} ⥤ C) (X : C) :
    IsColimit (⟨X, by tidy⟩ : Cocone F) ≃ ∀ Y : C, Unique (X ⟶ Y)
    where
  toFun t X :=
    { default := t.desc ⟨X, by tidy⟩
      uniq := fun f => t.uniq ⟨X, by tidy⟩ f (by tidy) }
  invFun u :=
    { desc := fun s => (u s.x).default
      uniq' := fun s _ _ => (u s.x).2 _ }
  left_inv := by tidy
  right_inv := by tidy
#align category_theory.limits.is_initial_equiv_unique CategoryTheory.Limits.isInitialEquivUnique

/-- An object `X` is initial if for every `Y` there is a unique morphism `X ⟶ Y`
    (as an instance). -/
def IsInitial.ofUnique (X : C) [h : ∀ Y : C, Unique (X ⟶ Y)] : IsInitial X
    where desc s := (h s.x).default
#align category_theory.limits.is_initial.of_unique CategoryTheory.Limits.IsInitial.ofUnique

/-- If `α` is a preorder with bot, then `⊥` is an initial object. -/
def isInitialBot {α : Type _} [Preorder α] [OrderBot α] : IsInitial (⊥ : α) :=
  IsInitial.ofUnique _
#align category_theory.limits.is_initial_bot CategoryTheory.Limits.isInitialBot

/-- Transport a term of type `is_initial` across an isomorphism. -/
def IsInitial.ofIso {X Y : C} (hX : IsInitial X) (i : X ≅ Y) : IsInitial Y :=
  IsColimit.ofIsoColimit hX
    { Hom := { Hom := i.Hom }
      inv := { Hom := i.inv } }
#align category_theory.limits.is_initial.of_iso CategoryTheory.Limits.IsInitial.ofIso

/-- Give the morphism to a terminal object from any other. -/
def IsTerminal.from {X : C} (t : IsTerminal X) (Y : C) : Y ⟶ X :=
  t.lift (asEmptyCone Y)
#align category_theory.limits.is_terminal.from CategoryTheory.Limits.IsTerminal.from

/-- Any two morphisms to a terminal object are equal. -/
theorem IsTerminal.hom_ext {X Y : C} (t : IsTerminal X) (f g : Y ⟶ X) : f = g :=
  t.hom_ext (by tidy)
#align category_theory.limits.is_terminal.hom_ext CategoryTheory.Limits.IsTerminal.hom_ext

@[simp]
theorem IsTerminal.comp_from {Z : C} (t : IsTerminal Z) {X Y : C} (f : X ⟶ Y) :
    f ≫ t.from Y = t.from X :=
  t.hom_ext _ _
#align category_theory.limits.is_terminal.comp_from CategoryTheory.Limits.IsTerminal.comp_from

@[simp]
theorem IsTerminal.from_self {X : C} (t : IsTerminal X) : t.from X = 𝟙 X :=
  t.hom_ext _ _
#align category_theory.limits.is_terminal.from_self CategoryTheory.Limits.IsTerminal.from_self

/-- Give the morphism from an initial object to any other. -/
def IsInitial.to {X : C} (t : IsInitial X) (Y : C) : X ⟶ Y :=
  t.desc (asEmptyCocone Y)
#align category_theory.limits.is_initial.to CategoryTheory.Limits.IsInitial.to

/-- Any two morphisms from an initial object are equal. -/
theorem IsInitial.hom_ext {X Y : C} (t : IsInitial X) (f g : X ⟶ Y) : f = g :=
  t.hom_ext (by tidy)
#align category_theory.limits.is_initial.hom_ext CategoryTheory.Limits.IsInitial.hom_ext

@[simp]
theorem IsInitial.to_comp {X : C} (t : IsInitial X) {Y Z : C} (f : Y ⟶ Z) : t.to Y ≫ f = t.to Z :=
  t.hom_ext _ _
#align category_theory.limits.is_initial.to_comp CategoryTheory.Limits.IsInitial.to_comp

@[simp]
theorem IsInitial.to_self {X : C} (t : IsInitial X) : t.to X = 𝟙 X :=
  t.hom_ext _ _
#align category_theory.limits.is_initial.to_self CategoryTheory.Limits.IsInitial.to_self

/-- Any morphism from a terminal object is split mono. -/
theorem IsTerminal.is_split_mono_from {X Y : C} (t : IsTerminal X) (f : X ⟶ Y) : IsSplitMono f :=
  IsSplitMono.mk' ⟨t.from _, t.hom_ext _ _⟩
#align
  category_theory.limits.is_terminal.is_split_mono_from CategoryTheory.Limits.IsTerminal.is_split_mono_from

/-- Any morphism to an initial object is split epi. -/
theorem IsInitial.is_split_epi_to {X Y : C} (t : IsInitial X) (f : Y ⟶ X) : IsSplitEpi f :=
  IsSplitEpi.mk' ⟨t.to _, t.hom_ext _ _⟩
#align
  category_theory.limits.is_initial.is_split_epi_to CategoryTheory.Limits.IsInitial.is_split_epi_to

/-- Any morphism from a terminal object is mono. -/
theorem IsTerminal.mono_from {X Y : C} (t : IsTerminal X) (f : X ⟶ Y) : Mono f := by
  haveI := t.is_split_mono_from f <;> infer_instance
#align category_theory.limits.is_terminal.mono_from CategoryTheory.Limits.IsTerminal.mono_from

/-- Any morphism to an initial object is epi. -/
theorem IsInitial.epi_to {X Y : C} (t : IsInitial X) (f : Y ⟶ X) : Epi f := by
  haveI := t.is_split_epi_to f <;> infer_instance
#align category_theory.limits.is_initial.epi_to CategoryTheory.Limits.IsInitial.epi_to

/-- If `T` and `T'` are terminal, they are isomorphic. -/
@[simps]
def IsTerminal.uniqueUpToIso {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T') : T ≅ T'
    where
  Hom := hT'.from _
  inv := hT.from _
#align
  category_theory.limits.is_terminal.unique_up_to_iso CategoryTheory.Limits.IsTerminal.uniqueUpToIso

/-- If `I` and `I'` are initial, they are isomorphic. -/
@[simps]
def IsInitial.uniqueUpToIso {I I' : C} (hI : IsInitial I) (hI' : IsInitial I') : I ≅ I'
    where
  Hom := hI.to _
  inv := hI'.to _
#align
  category_theory.limits.is_initial.unique_up_to_iso CategoryTheory.Limits.IsInitial.uniqueUpToIso

variable (C)

/-- A category has a terminal object if it has a limit over the empty diagram.
Use `has_terminal_of_unique` to construct instances.
-/
abbrev HasTerminal :=
  HasLimitsOfShape (Discrete.{0} PEmpty) C
#align category_theory.limits.has_terminal CategoryTheory.Limits.HasTerminal

/-- A category has an initial object if it has a colimit over the empty diagram.
Use `has_initial_of_unique` to construct instances.
-/
abbrev HasInitial :=
  HasColimitsOfShape (Discrete.{0} PEmpty) C
#align category_theory.limits.has_initial CategoryTheory.Limits.HasInitial

section Univ

variable (X : C) {F₁ : Discrete.{w} PEmpty ⥤ C} {F₂ : Discrete.{w'} PEmpty ⥤ C}

/-- Being terminal is independent of the empty diagram, its universe, and the cone over it,
    as long as the cone points are isomorphic. -/
def isLimitChangeEmptyCone {c₁ : Cone F₁} (hl : IsLimit c₁) (c₂ : Cone F₂) (hi : c₁.x ≅ c₂.x) :
    IsLimit c₂ where
  lift c := hl.lift ⟨c.x, by tidy⟩ ≫ hi.Hom
  fac' _ j := j.as.elim
  uniq' c f _ := by
    erw [← hl.uniq ⟨c.X, by tidy⟩ (f ≫ hi.inv) fun j => j.as.elim]
    simp
#align
  category_theory.limits.is_limit_change_empty_cone CategoryTheory.Limits.isLimitChangeEmptyCone

/-- Replacing an empty cone in `is_limit` by another with the same cone point
    is an equivalence. -/
def isLimitEmptyConeEquiv (c₁ : Cone F₁) (c₂ : Cone F₂) (h : c₁.x ≅ c₂.x) : IsLimit c₁ ≃ IsLimit c₂
    where
  toFun hl := isLimitChangeEmptyCone C hl c₂ h
  invFun hl := isLimitChangeEmptyCone C hl c₁ h.symm
  left_inv := by tidy
  right_inv := by tidy
#align category_theory.limits.is_limit_empty_cone_equiv CategoryTheory.Limits.isLimitEmptyConeEquiv

theorem hasTerminalChangeDiagram (h : HasLimit F₁) : HasLimit F₂ :=
  ⟨⟨⟨⟨limit F₁, by tidy⟩, isLimitChangeEmptyCone C (limit.isLimit F₁) _ (eqToIso rfl)⟩⟩⟩
#align
  category_theory.limits.has_terminal_change_diagram CategoryTheory.Limits.hasTerminalChangeDiagram

theorem hasTerminalChangeUniverse [h : HasLimitsOfShape (Discrete.{w} PEmpty) C] :
    HasLimitsOfShape (Discrete.{w'} PEmpty) C :=
  {
    HasLimit := fun J =>
      hasTerminalChangeDiagram C
        (let f := h.1
        f (Functor.empty C)) }
#align
  category_theory.limits.has_terminal_change_universe CategoryTheory.Limits.hasTerminalChangeUniverse

/-- Being initial is independent of the empty diagram, its universe, and the cocone over it,
    as long as the cocone points are isomorphic. -/
def isColimitChangeEmptyCocone {c₁ : Cocone F₁} (hl : IsColimit c₁) (c₂ : Cocone F₂)
    (hi : c₁.x ≅ c₂.x) : IsColimit c₂
    where
  desc c := hi.inv ≫ hl.desc ⟨c.x, by tidy⟩
  fac' _ j := j.as.elim
  uniq' c f _ := by
    erw [← hl.uniq ⟨c.X, by tidy⟩ (hi.hom ≫ f) fun j => j.as.elim]
    simp
#align
  category_theory.limits.is_colimit_change_empty_cocone CategoryTheory.Limits.isColimitChangeEmptyCocone

/-- Replacing an empty cocone in `is_colimit` by another with the same cocone point
    is an equivalence. -/
def isColimitEmptyCoconeEquiv (c₁ : Cocone F₁) (c₂ : Cocone F₂) (h : c₁.x ≅ c₂.x) :
    IsColimit c₁ ≃ IsColimit c₂
    where
  toFun hl := isColimitChangeEmptyCocone C hl c₂ h
  invFun hl := isColimitChangeEmptyCocone C hl c₁ h.symm
  left_inv := by tidy
  right_inv := by tidy
#align
  category_theory.limits.is_colimit_empty_cocone_equiv CategoryTheory.Limits.isColimitEmptyCoconeEquiv

theorem hasInitialChangeDiagram (h : HasColimit F₁) : HasColimit F₂ :=
  ⟨⟨⟨⟨colimit F₁, by tidy⟩, isColimitChangeEmptyCocone C (colimit.isColimit F₁) _ (eqToIso rfl)⟩⟩⟩
#align
  category_theory.limits.has_initial_change_diagram CategoryTheory.Limits.hasInitialChangeDiagram

theorem hasInitialChangeUniverse [h : HasColimitsOfShape (Discrete.{w} PEmpty) C] :
    HasColimitsOfShape (Discrete.{w'} PEmpty) C :=
  {
    HasColimit := fun J =>
      hasInitialChangeDiagram C
        (let f := h.1
        f (Functor.empty C)) }
#align
  category_theory.limits.has_initial_change_universe CategoryTheory.Limits.hasInitialChangeUniverse

end Univ

/-- An arbitrary choice of terminal object, if one exists.
You can use the notation `⊤_ C`.
This object is characterized by having a unique morphism from any object.
-/
abbrev terminal [HasTerminal C] : C :=
  limit (Functor.empty.{0} C)
#align category_theory.limits.terminal CategoryTheory.Limits.terminal

/-- An arbitrary choice of initial object, if one exists.
You can use the notation `⊥_ C`.
This object is characterized by having a unique morphism to any object.
-/
abbrev initial [HasInitial C] : C :=
  colimit (Functor.empty.{0} C)
#align category_theory.limits.initial CategoryTheory.Limits.initial

-- mathport name: «expr⊤_ »
notation "⊤_ " C:20 => terminal C

-- mathport name: «expr⊥_ »
notation "⊥_ " C:20 => initial C

section

variable {C}

/-- We can more explicitly show that a category has a terminal object by specifying the object,
and showing there is a unique morphism to it from any other object. -/
theorem has_terminal_of_unique (X : C) [h : ∀ Y : C, Unique (Y ⟶ X)] : HasTerminal C :=
  { HasLimit := fun F => HasLimit.mk ⟨_, (isTerminalEquivUnique F X).invFun h⟩ }
#align category_theory.limits.has_terminal_of_unique CategoryTheory.Limits.has_terminal_of_unique

theorem IsTerminal.has_terminal {X : C} (h : IsTerminal X) : HasTerminal C :=
  { HasLimit := fun F => HasLimit.mk ⟨⟨X, by tidy⟩, isLimitChangeEmptyCone _ h _ (Iso.refl _)⟩ }
#align category_theory.limits.is_terminal.has_terminal CategoryTheory.Limits.IsTerminal.has_terminal

/-- We can more explicitly show that a category has an initial object by specifying the object,
and showing there is a unique morphism from it to any other object. -/
theorem has_initial_of_unique (X : C) [h : ∀ Y : C, Unique (X ⟶ Y)] : HasInitial C :=
  { HasColimit := fun F => HasColimit.mk ⟨_, (isInitialEquivUnique F X).invFun h⟩ }
#align category_theory.limits.has_initial_of_unique CategoryTheory.Limits.has_initial_of_unique

theorem IsInitial.has_initial {X : C} (h : IsInitial X) : HasInitial C :=
  {
    HasColimit := fun F =>
      HasColimit.mk ⟨⟨X, by tidy⟩, isColimitChangeEmptyCocone _ h _ (Iso.refl _)⟩ }
#align category_theory.limits.is_initial.has_initial CategoryTheory.Limits.IsInitial.has_initial

/-- The map from an object to the terminal object. -/
abbrev terminal.from [HasTerminal C] (P : C) : P ⟶ ⊤_ C :=
  limit.lift (Functor.empty C) (asEmptyCone P)
#align category_theory.limits.terminal.from CategoryTheory.Limits.terminal.from

/-- The map to an object from the initial object. -/
abbrev initial.to [HasInitial C] (P : C) : ⊥_ C ⟶ P :=
  colimit.desc (Functor.empty C) (asEmptyCocone P)
#align category_theory.limits.initial.to CategoryTheory.Limits.initial.to

/-- A terminal object is terminal. -/
def terminalIsTerminal [HasTerminal C] : IsTerminal (⊤_ C) where lift s := terminal.from _
#align category_theory.limits.terminal_is_terminal CategoryTheory.Limits.terminalIsTerminal

/-- An initial object is initial. -/
def initialIsInitial [HasInitial C] : IsInitial (⊥_ C) where desc s := initial.to _
#align category_theory.limits.initial_is_initial CategoryTheory.Limits.initialIsInitial

instance uniqueToTerminal [HasTerminal C] (P : C) : Unique (P ⟶ ⊤_ C) :=
  isTerminalEquivUnique _ (⊤_ C) terminalIsTerminal P
#align category_theory.limits.unique_to_terminal CategoryTheory.Limits.uniqueToTerminal

instance uniqueFromInitial [HasInitial C] (P : C) : Unique (⊥_ C ⟶ P) :=
  isInitialEquivUnique _ (⊥_ C) initialIsInitial P
#align category_theory.limits.unique_from_initial CategoryTheory.Limits.uniqueFromInitial

@[simp]
theorem terminal.comp_from [HasTerminal C] {P Q : C} (f : P ⟶ Q) :
    f ≫ terminal.from Q = terminal.from P := by tidy
#align category_theory.limits.terminal.comp_from CategoryTheory.Limits.terminal.comp_from

@[simp]
theorem initial.to_comp [HasInitial C] {P Q : C} (f : P ⟶ Q) : initial.to P ≫ f = initial.to Q := by
  tidy
#align category_theory.limits.initial.to_comp CategoryTheory.Limits.initial.to_comp

/-- The (unique) isomorphism between the chosen initial object and any other initial object. -/
@[simp]
def initialIsoIsInitial [HasInitial C] {P : C} (t : IsInitial P) : ⊥_ C ≅ P :=
  initialIsInitial.uniqueUpToIso t
#align category_theory.limits.initial_iso_is_initial CategoryTheory.Limits.initialIsoIsInitial

/-- The (unique) isomorphism between the chosen terminal object and any other terminal object. -/
@[simp]
def terminalIsoIsTerminal [HasTerminal C] {P : C} (t : IsTerminal P) : ⊤_ C ≅ P :=
  terminalIsTerminal.uniqueUpToIso t
#align category_theory.limits.terminal_iso_is_terminal CategoryTheory.Limits.terminalIsoIsTerminal

/-- Any morphism from a terminal object is split mono. -/
instance terminal.is_split_mono_from {Y : C} [HasTerminal C] (f : ⊤_ C ⟶ Y) : IsSplitMono f :=
  IsTerminal.is_split_mono_from terminalIsTerminal _
#align
  category_theory.limits.terminal.is_split_mono_from CategoryTheory.Limits.terminal.is_split_mono_from

/-- Any morphism to an initial object is split epi. -/
instance initial.is_split_epi_to {Y : C} [HasInitial C] (f : Y ⟶ ⊥_ C) : IsSplitEpi f :=
  IsInitial.is_split_epi_to initialIsInitial _
#align category_theory.limits.initial.is_split_epi_to CategoryTheory.Limits.initial.is_split_epi_to

/-- An initial object is terminal in the opposite category. -/
def terminalOpOfInitial {X : C} (t : IsInitial X) : IsTerminal (Opposite.op X)
    where
  lift s := (t.to s.x.unop).op
  uniq' s m w := Quiver.Hom.unop_inj (t.hom_ext _ _)
#align category_theory.limits.terminal_op_of_initial CategoryTheory.Limits.terminalOpOfInitial

/-- An initial object in the opposite category is terminal in the original category. -/
def terminalUnopOfInitial {X : Cᵒᵖ} (t : IsInitial X) : IsTerminal X.unop
    where
  lift s := (t.to (Opposite.op s.x)).unop
  uniq' s m w := Quiver.Hom.op_inj (t.hom_ext _ _)
#align category_theory.limits.terminal_unop_of_initial CategoryTheory.Limits.terminalUnopOfInitial

/-- A terminal object is initial in the opposite category. -/
def initialOpOfTerminal {X : C} (t : IsTerminal X) : IsInitial (Opposite.op X)
    where
  desc s := (t.from s.x.unop).op
  uniq' s m w := Quiver.Hom.unop_inj (t.hom_ext _ _)
#align category_theory.limits.initial_op_of_terminal CategoryTheory.Limits.initialOpOfTerminal

/-- A terminal object in the opposite category is initial in the original category. -/
def initialUnopOfTerminal {X : Cᵒᵖ} (t : IsTerminal X) : IsInitial X.unop
    where
  desc s := (t.from (Opposite.op s.x)).unop
  uniq' s m w := Quiver.Hom.op_inj (t.hom_ext _ _)
#align category_theory.limits.initial_unop_of_terminal CategoryTheory.Limits.initialUnopOfTerminal

instance has_initial_op_of_has_terminal [HasTerminal C] : HasInitial Cᵒᵖ :=
  (initialOpOfTerminal terminalIsTerminal).HasInitial
#align
  category_theory.limits.has_initial_op_of_has_terminal CategoryTheory.Limits.has_initial_op_of_has_terminal

instance has_terminal_op_of_has_initial [HasInitial C] : HasTerminal Cᵒᵖ :=
  (terminalOpOfInitial initialIsInitial).HasTerminal
#align
  category_theory.limits.has_terminal_op_of_has_initial CategoryTheory.Limits.has_terminal_op_of_has_initial

theorem has_terminal_of_has_initial_op [HasInitial Cᵒᵖ] : HasTerminal C :=
  (terminalUnopOfInitial initialIsInitial).HasTerminal
#align
  category_theory.limits.has_terminal_of_has_initial_op CategoryTheory.Limits.has_terminal_of_has_initial_op

theorem has_initial_of_has_terminal_op [HasTerminal Cᵒᵖ] : HasInitial C :=
  (initialUnopOfTerminal terminalIsTerminal).HasInitial
#align
  category_theory.limits.has_initial_of_has_terminal_op CategoryTheory.Limits.has_initial_of_has_terminal_op

instance {J : Type _} [Category J] {C : Type _} [Category C] [HasTerminal C] :
    HasLimit ((CategoryTheory.Functor.const J).obj (⊤_ C)) :=
  HasLimit.mk
    { Cone :=
        { x := ⊤_ C
          π := { app := fun _ => terminal.from _ } }
      IsLimit := { lift := fun s => terminal.from _ } }

/-- The limit of the constant `⊤_ C` functor is `⊤_ C`. -/
@[simps Hom]
def limitConstTerminal {J : Type _} [Category J] {C : Type _} [Category C] [HasTerminal C] :
    limit ((CategoryTheory.Functor.const J).obj (⊤_ C)) ≅ ⊤_ C
    where
  Hom := terminal.from _
  inv :=
    limit.lift ((CategoryTheory.Functor.const J).obj (⊤_ C))
      { x := ⊤_ C
        π := { app := fun j => terminal.from _ } }
#align category_theory.limits.limit_const_terminal CategoryTheory.Limits.limitConstTerminal

@[simp, reassoc.1]
theorem limit_const_terminal_inv_π {J : Type _} [Category J] {C : Type _} [Category C]
    [HasTerminal C] {j : J} :
    limitConstTerminal.inv ≫ limit.π ((CategoryTheory.Functor.const J).obj (⊤_ C)) j =
      terminal.from _ :=
  by ext ⟨⟨⟩⟩
#align
  category_theory.limits.limit_const_terminal_inv_π CategoryTheory.Limits.limit_const_terminal_inv_π

instance {J : Type _} [Category J] {C : Type _} [Category C] [HasInitial C] :
    HasColimit ((CategoryTheory.Functor.const J).obj (⊥_ C)) :=
  HasColimit.mk
    { Cocone :=
        { x := ⊥_ C
          ι := { app := fun _ => initial.to _ } }
      IsColimit := { desc := fun s => initial.to _ } }

/-- The colimit of the constant `⊥_ C` functor is `⊥_ C`. -/
@[simps inv]
def colimitConstInitial {J : Type _} [Category J] {C : Type _} [Category C] [HasInitial C] :
    colimit ((CategoryTheory.Functor.const J).obj (⊥_ C)) ≅ ⊥_ C
    where
  Hom :=
    colimit.desc ((CategoryTheory.Functor.const J).obj (⊥_ C))
      { x := ⊥_ C
        ι := { app := fun j => initial.to _ } }
  inv := initial.to _
#align category_theory.limits.colimit_const_initial CategoryTheory.Limits.colimitConstInitial

@[simp, reassoc.1]
theorem ι_colimit_const_initial_hom {J : Type _} [Category J] {C : Type _} [Category C]
    [HasInitial C] {j : J} :
    colimit.ι ((CategoryTheory.Functor.const J).obj (⊥_ C)) j ≫ colimitConstInitial.Hom =
      initial.to _ :=
  by ext ⟨⟨⟩⟩
#align
  category_theory.limits.ι_colimit_const_initial_hom CategoryTheory.Limits.ι_colimit_const_initial_hom

/-- A category is a `initial_mono_class` if the canonical morphism of an initial object is a
monomorphism.  In practice, this is most useful when given an arbitrary morphism out of the chosen
initial object, see `initial.mono_from`.
Given a terminal object, this is equivalent to the assumption that the unique morphism from initial
to terminal is a monomorphism, which is the second of Freyd's axioms for an AT category.

TODO: This is a condition satisfied by categories with zero objects and morphisms.
-/
class InitialMonoClass (C : Type u₁) [Category.{v₁} C] : Prop where
  is_initial_mono_from : ∀ {I} (X : C) (hI : IsInitial I), Mono (hI.to X)
#align category_theory.limits.initial_mono_class CategoryTheory.Limits.InitialMonoClass

theorem IsInitial.mono_from [InitialMonoClass C] {I} {X : C} (hI : IsInitial I) (f : I ⟶ X) :
    Mono f := by
  rw [hI.hom_ext f (hI.to X)]
  apply initial_mono_class.is_initial_mono_from
#align category_theory.limits.is_initial.mono_from CategoryTheory.Limits.IsInitial.mono_from

instance (priority := 100) initial.mono_from [HasInitial C] [InitialMonoClass C] (X : C)
    (f : ⊥_ C ⟶ X) : Mono f :=
  initialIsInitial.mono_from f
#align category_theory.limits.initial.mono_from CategoryTheory.Limits.initial.mono_from

/-- To show a category is a `initial_mono_class` it suffices to give an initial object such that
every morphism out of it is a monomorphism. -/
theorem InitialMonoClass.of_is_initial {I : C} (hI : IsInitial I) (h : ∀ X, Mono (hI.to X)) :
    InitialMonoClass C :=
  {
    is_initial_mono_from := fun I' X hI' =>
      by
      rw [hI'.hom_ext (hI'.to X) ((hI'.unique_up_to_iso hI).Hom ≫ hI.to X)]
      apply mono_comp }
#align
  category_theory.limits.initial_mono_class.of_is_initial CategoryTheory.Limits.InitialMonoClass.of_is_initial

/-- To show a category is a `initial_mono_class` it suffices to show every morphism out of the
initial object is a monomorphism. -/
theorem InitialMonoClass.of_initial [HasInitial C] (h : ∀ X : C, Mono (initial.to X)) :
    InitialMonoClass C :=
  InitialMonoClass.of_is_initial initialIsInitial h
#align
  category_theory.limits.initial_mono_class.of_initial CategoryTheory.Limits.InitialMonoClass.of_initial

/-- To show a category is a `initial_mono_class` it suffices to show the unique morphism from an
initial object to a terminal object is a monomorphism. -/
theorem InitialMonoClass.of_is_terminal {I T : C} (hI : IsInitial I) (hT : IsTerminal T)
    (f : Mono (hI.to T)) : InitialMonoClass C :=
  InitialMonoClass.of_is_initial hI fun X => mono_of_mono_fac (hI.hom_ext (_ ≫ hT.from X) (hI.to T))
#align
  category_theory.limits.initial_mono_class.of_is_terminal CategoryTheory.Limits.InitialMonoClass.of_is_terminal

/-- To show a category is a `initial_mono_class` it suffices to show the unique morphism from the
initial object to a terminal object is a monomorphism. -/
theorem InitialMonoClass.of_terminal [HasInitial C] [HasTerminal C] (h : Mono (initial.to (⊤_ C))) :
    InitialMonoClass C :=
  InitialMonoClass.of_is_terminal initialIsInitial terminalIsTerminal h
#align
  category_theory.limits.initial_mono_class.of_terminal CategoryTheory.Limits.InitialMonoClass.of_terminal

section Comparison

variable {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)

/-- The comparison morphism from the image of a terminal object to the terminal object in the target
category.
This is an isomorphism iff `G` preserves terminal objects, see
`category_theory.limits.preserves_terminal.of_iso_comparison`.
-/
def terminalComparison [HasTerminal C] [HasTerminal D] : G.obj (⊤_ C) ⟶ ⊤_ D :=
  terminal.from _
#align category_theory.limits.terminal_comparison CategoryTheory.Limits.terminalComparison

-- TODO: Show this is an isomorphism if and only if `G` preserves initial objects.
/--
The comparison morphism from the initial object in the target category to the image of the initial
object.
-/
def initialComparison [HasInitial C] [HasInitial D] : ⊥_ D ⟶ G.obj (⊥_ C) :=
  initial.to _
#align category_theory.limits.initial_comparison CategoryTheory.Limits.initialComparison

end Comparison

variable {J : Type u} [Category.{v} J]

/-- From a functor `F : J ⥤ C`, given an initial object of `J`, construct a cone for `J`.
In `limit_of_diagram_initial` we show it is a limit cone. -/
@[simps]
def coneOfDiagramInitial {X : J} (tX : IsInitial X) (F : J ⥤ C) : Cone F
    where
  x := F.obj X
  π :=
    { app := fun j => F.map (tX.to j)
      naturality' := fun j j' k => by
        dsimp
        rw [← F.map_comp, category.id_comp, tX.hom_ext (tX.to j ≫ k) (tX.to j')] }
#align category_theory.limits.cone_of_diagram_initial CategoryTheory.Limits.coneOfDiagramInitial

/-- From a functor `F : J ⥤ C`, given an initial object of `J`, show the cone
`cone_of_diagram_initial` is a limit. -/
def limitOfDiagramInitial {X : J} (tX : IsInitial X) (F : J ⥤ C) :
    IsLimit (coneOfDiagramInitial tX F)
    where
  lift s := s.π.app X
  uniq' s m w :=
    by
    rw [← w X, cone_of_diagram_initial_π_app, tX.hom_ext (tX.to X) (𝟙 _)]
    dsimp; simp
#align category_theory.limits.limit_of_diagram_initial CategoryTheory.Limits.limitOfDiagramInitial

-- See note [dsimp, simp]
-- This is reducible to allow usage of lemmas about `cone_point_unique_up_to_iso`.
/-- For a functor `F : J ⥤ C`, if `J` has an initial object then the image of it is isomorphic
to the limit of `F`. -/
@[reducible]
def limitOfInitial (F : J ⥤ C) [HasInitial J] [HasLimit F] : limit F ≅ F.obj (⊥_ J) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitOfDiagramInitial initialIsInitial F)
#align category_theory.limits.limit_of_initial CategoryTheory.Limits.limitOfInitial

/-- From a functor `F : J ⥤ C`, given a terminal object of `J`, construct a cone for `J`,
provided that the morphisms in the diagram are isomorphisms.
In `limit_of_diagram_terminal` we show it is a limit cone. -/
@[simps]
def coneOfDiagramTerminal {X : J} (hX : IsTerminal X) (F : J ⥤ C)
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : Cone F
    where
  x := F.obj X
  π :=
    { app := fun i => inv (F.map (hX.from _))
      naturality' := by
        intro i j f
        dsimp
        simp only [is_iso.eq_inv_comp, is_iso.comp_inv_eq, category.id_comp, ← F.map_comp,
          hX.hom_ext (hX.from i) (f ≫ hX.from j)] }
#align category_theory.limits.cone_of_diagram_terminal CategoryTheory.Limits.coneOfDiagramTerminal

/-- From a functor `F : J ⥤ C`, given a terminal object of `J` and that the morphisms in the
diagram are isomorphisms, show the cone `cone_of_diagram_terminal` is a limit. -/
def limitOfDiagramTerminal {X : J} (hX : IsTerminal X) (F : J ⥤ C)
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : IsLimit (coneOfDiagramTerminal hX F)
    where lift S := S.π.app _
#align category_theory.limits.limit_of_diagram_terminal CategoryTheory.Limits.limitOfDiagramTerminal

-- This is reducible to allow usage of lemmas about `cone_point_unique_up_to_iso`.
/-- For a functor `F : J ⥤ C`, if `J` has a terminal object and all the morphisms in the diagram
are isomorphisms, then the image of the terminal object is isomorphic to the limit of `F`. -/
@[reducible]
def limitOfTerminal (F : J ⥤ C) [HasTerminal J] [HasLimit F]
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : limit F ≅ F.obj (⊤_ J) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitOfDiagramTerminal terminalIsTerminal F)
#align category_theory.limits.limit_of_terminal CategoryTheory.Limits.limitOfTerminal

/-- From a functor `F : J ⥤ C`, given a terminal object of `J`, construct a cocone for `J`.
In `colimit_of_diagram_terminal` we show it is a colimit cocone. -/
@[simps]
def coconeOfDiagramTerminal {X : J} (tX : IsTerminal X) (F : J ⥤ C) : Cocone F
    where
  x := F.obj X
  ι :=
    { app := fun j => F.map (tX.from j)
      naturality' := fun j j' k => by
        dsimp
        rw [← F.map_comp, category.comp_id, tX.hom_ext (k ≫ tX.from j') (tX.from j)] }
#align
  category_theory.limits.cocone_of_diagram_terminal CategoryTheory.Limits.coconeOfDiagramTerminal

/-- From a functor `F : J ⥤ C`, given a terminal object of `J`, show the cocone
`cocone_of_diagram_terminal` is a colimit. -/
def colimitOfDiagramTerminal {X : J} (tX : IsTerminal X) (F : J ⥤ C) :
    IsColimit (coconeOfDiagramTerminal tX F)
    where
  desc s := s.ι.app X
  uniq' s m w :=
    by
    rw [← w X, cocone_of_diagram_terminal_ι_app, tX.hom_ext (tX.from X) (𝟙 _)]
    simp
#align
  category_theory.limits.colimit_of_diagram_terminal CategoryTheory.Limits.colimitOfDiagramTerminal

-- This is reducible to allow usage of lemmas about `cocone_point_unique_up_to_iso`.
/-- For a functor `F : J ⥤ C`, if `J` has a terminal object then the image of it is isomorphic
to the colimit of `F`. -/
@[reducible]
def colimitOfTerminal (F : J ⥤ C) [HasTerminal J] [HasColimit F] : colimit F ≅ F.obj (⊤_ J) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (colimitOfDiagramTerminal terminalIsTerminal F)
#align category_theory.limits.colimit_of_terminal CategoryTheory.Limits.colimitOfTerminal

/-- From a functor `F : J ⥤ C`, given an initial object of `J`, construct a cocone for `J`,
provided that the morphisms in the diagram are isomorphisms.
In `colimit_of_diagram_initial` we show it is a colimit cocone. -/
@[simps]
def coconeOfDiagramInitial {X : J} (hX : IsInitial X) (F : J ⥤ C)
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : Cocone F
    where
  x := F.obj X
  ι :=
    { app := fun i => inv (F.map (hX.to _))
      naturality' := by
        intro i j f
        dsimp
        simp only [is_iso.eq_inv_comp, is_iso.comp_inv_eq, category.comp_id, ← F.map_comp,
          hX.hom_ext (hX.to i ≫ f) (hX.to j)] }
#align category_theory.limits.cocone_of_diagram_initial CategoryTheory.Limits.coconeOfDiagramInitial

/-- From a functor `F : J ⥤ C`, given an initial object of `J` and that the morphisms in the
diagram are isomorphisms, show the cone `cocone_of_diagram_initial` is a colimit. -/
def colimitOfDiagramInitial {X : J} (hX : IsInitial X) (F : J ⥤ C)
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : IsColimit (coconeOfDiagramInitial hX F)
    where desc S := S.ι.app _
#align
  category_theory.limits.colimit_of_diagram_initial CategoryTheory.Limits.colimitOfDiagramInitial

-- This is reducible to allow usage of lemmas about `cocone_point_unique_up_to_iso`.
/-- For a functor `F : J ⥤ C`, if `J` has an initial object and all the morphisms in the diagram
are isomorphisms, then the image of the initial object is isomorphic to the colimit of `F`. -/
@[reducible]
def colimitOfInitial (F : J ⥤ C) [HasInitial J] [HasColimit F]
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : colimit F ≅ F.obj (⊥_ J) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (colimitOfDiagramInitial initialIsInitial _)
#align category_theory.limits.colimit_of_initial CategoryTheory.Limits.colimitOfInitial

/-- If `j` is initial in the index category, then the map `limit.π F j` is an isomorphism.
-/
theorem is_iso_π_of_is_initial {j : J} (I : IsInitial j) (F : J ⥤ C) [HasLimit F] :
    IsIso (limit.π F j) :=
  ⟨⟨limit.lift _ (coneOfDiagramInitial I F),
      ⟨by
        ext
        simp, by simp⟩⟩⟩
#align category_theory.limits.is_iso_π_of_is_initial CategoryTheory.Limits.is_iso_π_of_is_initial

instance is_iso_π_initial [HasInitial J] (F : J ⥤ C) [HasLimit F] : IsIso (limit.π F (⊥_ J)) :=
  is_iso_π_of_is_initial initialIsInitial F
#align category_theory.limits.is_iso_π_initial CategoryTheory.Limits.is_iso_π_initial

theorem is_iso_π_of_is_terminal {j : J} (I : IsTerminal j) (F : J ⥤ C) [HasLimit F]
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : IsIso (limit.π F j) :=
  ⟨⟨limit.lift _ (coneOfDiagramTerminal I F), by
      ext
      simp, by simp⟩⟩
#align category_theory.limits.is_iso_π_of_is_terminal CategoryTheory.Limits.is_iso_π_of_is_terminal

instance is_iso_π_terminal [HasTerminal J] (F : J ⥤ C) [HasLimit F]
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : IsIso (limit.π F (⊤_ J)) :=
  is_iso_π_of_is_terminal terminalIsTerminal F
#align category_theory.limits.is_iso_π_terminal CategoryTheory.Limits.is_iso_π_terminal

/-- If `j` is terminal in the index category, then the map `colimit.ι F j` is an isomorphism.
-/
theorem is_iso_ι_of_is_terminal {j : J} (I : IsTerminal j) (F : J ⥤ C) [HasColimit F] :
    IsIso (colimit.ι F j) :=
  ⟨⟨colimit.desc _ (coconeOfDiagramTerminal I F),
      ⟨by simp, by
        ext
        simp⟩⟩⟩
#align category_theory.limits.is_iso_ι_of_is_terminal CategoryTheory.Limits.is_iso_ι_of_is_terminal

instance is_iso_ι_terminal [HasTerminal J] (F : J ⥤ C) [HasColimit F] :
    IsIso (colimit.ι F (⊤_ J)) :=
  is_iso_ι_of_is_terminal terminalIsTerminal F
#align category_theory.limits.is_iso_ι_terminal CategoryTheory.Limits.is_iso_ι_terminal

theorem is_iso_ι_of_is_initial {j : J} (I : IsInitial j) (F : J ⥤ C) [HasColimit F]
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : IsIso (colimit.ι F j) :=
  ⟨⟨colimit.desc _ (coconeOfDiagramInitial I F),
      ⟨by tidy, by
        ext
        simp⟩⟩⟩
#align category_theory.limits.is_iso_ι_of_is_initial CategoryTheory.Limits.is_iso_ι_of_is_initial

instance is_iso_ι_initial [HasInitial J] (F : J ⥤ C) [HasColimit F]
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : IsIso (colimit.ι F (⊥_ J)) :=
  is_iso_ι_of_is_initial initialIsInitial F
#align category_theory.limits.is_iso_ι_initial CategoryTheory.Limits.is_iso_ι_initial

end

end CategoryTheory.Limits

