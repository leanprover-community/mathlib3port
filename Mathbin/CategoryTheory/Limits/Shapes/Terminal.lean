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

/-- Construct a cone for the empty diagram given an object. -/
@[simps]
def as_empty_cone (X : C) : Cone (Functor.empty.{w} C) :=
  { x,
    π := by
      tidy }

/-- Construct a cocone for the empty diagram given an object. -/
@[simps]
def as_empty_cocone (X : C) : Cocone (Functor.empty.{w} C) :=
  { x,
    ι := by
      tidy }

/-- `X` is terminal if the cone it induces on the empty diagram is limiting. -/
abbrev is_terminal (X : C) :=
  IsLimit (asEmptyCone.{v₁} X)

/-- `X` is initial if the cocone it induces on the empty diagram is colimiting. -/
abbrev is_initial (X : C) :=
  IsColimit (asEmptyCocone.{v₁} X)

/-- An object `Y` is terminal iff for every `X` there is a unique morphism `X ⟶ Y`. -/
def is_terminal_equiv_unique (F : Discrete.{v₁} Pempty ⥤ C) (Y : C) :
    IsLimit
        (⟨Y, by
          tidy⟩ :
          Cone F) ≃
      ∀ X : C, Unique (X ⟶ Y) where
  toFun := fun t X =>
    { default :=
        t.lift
          ⟨X, by
            tidy⟩,
      uniq := fun f =>
        t.uniq
          ⟨X, by
            tidy⟩
          f
          (by
            tidy) }
  invFun := fun u => { lift := fun s => (u s.x).default, uniq' := fun s _ _ => (u s.x).2 _ }
  left_inv := by
    tidy
  right_inv := by
    tidy

/-- An object `Y` is terminal if for every `X` there is a unique morphism `X ⟶ Y`
    (as an instance). -/
def is_terminal.of_unique (Y : C) [h : ∀ X : C, Unique (X ⟶ Y)] : IsTerminal Y where
  lift := fun s => (h s.x).default

/-- If `α` is a preorder with top, then `⊤` is a terminal object. -/
def is_terminal_top {α : Type _} [Preorderₓ α] [OrderTop α] : IsTerminal (⊤ : α) :=
  IsTerminal.ofUnique _

/-- Transport a term of type `is_terminal` across an isomorphism. -/
def is_terminal.of_iso {Y Z : C} (hY : IsTerminal Y) (i : Y ≅ Z) : IsTerminal Z :=
  IsLimit.ofIsoLimit hY { Hom := { Hom := i.Hom }, inv := { Hom := i.inv } }

/-- An object `X` is initial iff for every `Y` there is a unique morphism `X ⟶ Y`. -/
def is_initial_equiv_unique (F : Discrete.{v₁} Pempty ⥤ C) (X : C) :
    IsColimit
        (⟨X, by
          tidy⟩ :
          Cocone F) ≃
      ∀ Y : C, Unique (X ⟶ Y) where
  toFun := fun t X =>
    { default :=
        t.desc
          ⟨X, by
            tidy⟩,
      uniq := fun f =>
        t.uniq
          ⟨X, by
            tidy⟩
          f
          (by
            tidy) }
  invFun := fun u => { desc := fun s => (u s.x).default, uniq' := fun s _ _ => (u s.x).2 _ }
  left_inv := by
    tidy
  right_inv := by
    tidy

/-- An object `X` is initial if for every `Y` there is a unique morphism `X ⟶ Y`
    (as an instance). -/
def is_initial.of_unique (X : C) [h : ∀ Y : C, Unique (X ⟶ Y)] : IsInitial X where
  desc := fun s => (h s.x).default

/-- If `α` is a preorder with bot, then `⊥` is an initial object. -/
def is_initial_bot {α : Type _} [Preorderₓ α] [OrderBot α] : IsInitial (⊥ : α) :=
  IsInitial.ofUnique _

/-- Transport a term of type `is_initial` across an isomorphism. -/
def is_initial.of_iso {X Y : C} (hX : IsInitial X) (i : X ≅ Y) : IsInitial Y :=
  IsColimit.ofIsoColimit hX { Hom := { Hom := i.Hom }, inv := { Hom := i.inv } }

/-- Give the morphism to a terminal object from any other. -/
def is_terminal.from {X : C} (t : IsTerminal X) (Y : C) : Y ⟶ X :=
  t.lift (asEmptyCone Y)

/-- Any two morphisms to a terminal object are equal. -/
theorem is_terminal.hom_ext {X Y : C} (t : IsTerminal X) (f g : Y ⟶ X) : f = g :=
  t.hom_ext
    (by
      tidy)

@[simp]
theorem is_terminal.comp_from {Z : C} (t : IsTerminal Z) {X Y : C} (f : X ⟶ Y) : f ≫ t.from Y = t.from X :=
  t.hom_ext _ _

@[simp]
theorem is_terminal.from_self {X : C} (t : IsTerminal X) : t.from X = 𝟙 X :=
  t.hom_ext _ _

/-- Give the morphism from an initial object to any other. -/
def is_initial.to {X : C} (t : IsInitial X) (Y : C) : X ⟶ Y :=
  t.desc (asEmptyCocone Y)

/-- Any two morphisms from an initial object are equal. -/
theorem is_initial.hom_ext {X Y : C} (t : IsInitial X) (f g : X ⟶ Y) : f = g :=
  t.hom_ext
    (by
      tidy)

@[simp]
theorem is_initial.to_comp {X : C} (t : IsInitial X) {Y Z : C} (f : Y ⟶ Z) : t.to Y ≫ f = t.to Z :=
  t.hom_ext _ _

@[simp]
theorem is_initial.to_self {X : C} (t : IsInitial X) : t.to X = 𝟙 X :=
  t.hom_ext _ _

/-- Any morphism from a terminal object is split mono. -/
def is_terminal.split_mono_from {X Y : C} (t : IsTerminal X) (f : X ⟶ Y) : SplitMono f :=
  ⟨t.from _, t.hom_ext _ _⟩

/-- Any morphism to an initial object is split epi. -/
def is_initial.split_epi_to {X Y : C} (t : IsInitial X) (f : Y ⟶ X) : SplitEpi f :=
  ⟨t.to _, t.hom_ext _ _⟩

/-- Any morphism from a terminal object is mono. -/
theorem is_terminal.mono_from {X Y : C} (t : IsTerminal X) (f : X ⟶ Y) : Mono f := by
  have := t.split_mono_from f <;> infer_instance

/-- Any morphism to an initial object is epi. -/
theorem is_initial.epi_to {X Y : C} (t : IsInitial X) (f : Y ⟶ X) : Epi f := by
  have := t.split_epi_to f <;> infer_instance

/-- If `T` and `T'` are terminal, they are isomorphic. -/
@[simps]
def is_terminal.unique_up_to_iso {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T') : T ≅ T' where
  Hom := hT'.from _
  inv := hT.from _

/-- If `I` and `I'` are initial, they are isomorphic. -/
@[simps]
def is_initial.unique_up_to_iso {I I' : C} (hI : IsInitial I) (hI' : IsInitial I') : I ≅ I' where
  Hom := hI.to _
  inv := hI'.to _

variable (C)

/-- A category has a terminal object if it has a limit over the empty diagram.
Use `has_terminal_of_unique` to construct instances.
-/
abbrev has_terminal :=
  HasLimitsOfShape (Discrete.{v₁} Pempty) C

/-- A category has an initial object if it has a colimit over the empty diagram.
Use `has_initial_of_unique` to construct instances.
-/
abbrev has_initial :=
  HasColimitsOfShape (Discrete.{v₁} Pempty) C

section Univ

variable (X : C) {F₁ : Discrete.{w} Pempty ⥤ C} {F₂ : Discrete.{w'} Pempty ⥤ C}

/-- Being terminal is independent of the empty diagram, its universe, and the cone over it,
    as long as the cone points are isomorphic. -/
def is_limit_change_empty_cone {c₁ : Cone F₁} (hl : IsLimit c₁) (c₂ : Cone F₂) (hi : c₁.x ≅ c₂.x) : IsLimit c₂ where
  lift := fun c =>
    hl.lift
        ⟨c.x, by
          tidy⟩ ≫
      hi.Hom
  fac' := fun _ j => j.elim
  uniq' := fun c f _ => by
    erw [←
      hl.uniq
        ⟨c.X, by
          tidy⟩
        (f ≫ hi.inv) fun j => j.elim]
    simp

/-- Replacing an empty cone in `is_limit` by another with the same cone point
    is an equivalence. -/
def is_limit_empty_cone_equiv (c₁ : Cone F₁) (c₂ : Cone F₂) (h : c₁.x ≅ c₂.x) : IsLimit c₁ ≃ IsLimit c₂ where
  toFun := fun hl => isLimitChangeEmptyCone C hl c₂ h
  invFun := fun hl => isLimitChangeEmptyCone C hl c₁ h.symm
  left_inv := by
    tidy
  right_inv := by
    tidy

theorem has_terminal_change_diagram (h : HasLimit F₁) : HasLimit F₂ :=
  ⟨⟨⟨⟨limit F₁, by
          tidy⟩,
        isLimitChangeEmptyCone C (limit.isLimit F₁) _ (eqToIso rfl)⟩⟩⟩

theorem has_terminal_change_universe [h : HasLimitsOfShape (Discrete.{w} Pempty) C] :
    HasLimitsOfShape (Discrete.{w'} Pempty) C :=
  { HasLimit := fun J =>
      has_terminal_change_diagram C
        (let f := h.1
        f (Functor.empty C)) }

/-- Being initial is independent of the empty diagram, its universe, and the cocone over it,
    as long as the cocone points are isomorphic. -/
def is_colimit_change_empty_cocone {c₁ : Cocone F₁} (hl : IsColimit c₁) (c₂ : Cocone F₂) (hi : c₁.x ≅ c₂.x) :
    IsColimit c₂ where
  desc := fun c =>
    hi.inv ≫
      hl.desc
        ⟨c.x, by
          tidy⟩
  fac' := fun _ j => j.elim
  uniq' := fun c f _ => by
    erw [←
      hl.uniq
        ⟨c.X, by
          tidy⟩
        (hi.hom ≫ f) fun j => j.elim]
    simp

/-- Replacing an empty cocone in `is_colimit` by another with the same cocone point
    is an equivalence. -/
def is_colimit_empty_cocone_equiv (c₁ : Cocone F₁) (c₂ : Cocone F₂) (h : c₁.x ≅ c₂.x) :
    IsColimit c₁ ≃ IsColimit c₂ where
  toFun := fun hl => isColimitChangeEmptyCocone C hl c₂ h
  invFun := fun hl => isColimitChangeEmptyCocone C hl c₁ h.symm
  left_inv := by
    tidy
  right_inv := by
    tidy

theorem has_initial_change_diagram (h : HasColimit F₁) : HasColimit F₂ :=
  ⟨⟨⟨⟨colimit F₁, by
          tidy⟩,
        isColimitChangeEmptyCocone C (colimit.isColimit F₁) _ (eqToIso rfl)⟩⟩⟩

theorem has_initial_change_universe [h : HasColimitsOfShape (Discrete.{w} Pempty) C] :
    HasColimitsOfShape (Discrete.{w'} Pempty) C :=
  { HasColimit := fun J =>
      has_initial_change_diagram C
        (let f := h.1
        f (Functor.empty C)) }

end Univ

/-- An arbitrary choice of terminal object, if one exists.
You can use the notation `⊤_ C`.
This object is characterized by having a unique morphism from any object.
-/
abbrev terminal [HasTerminal C] : C :=
  limit (Functor.empty.{v₁} C)

/-- An arbitrary choice of initial object, if one exists.
You can use the notation `⊥_ C`.
This object is characterized by having a unique morphism to any object.
-/
abbrev initial [HasInitial C] : C :=
  colimit (Functor.empty.{v₁} C)

notation "⊤_ " C:20 => terminal C

notation "⊥_ " C:20 => initial C

section

variable {C}

/-- We can more explicitly show that a category has a terminal object by specifying the object,
and showing there is a unique morphism to it from any other object. -/
theorem has_terminal_of_unique (X : C) [h : ∀ Y : C, Unique (Y ⟶ X)] : HasTerminal C :=
  { HasLimit := fun F => HasLimit.mk ⟨_, (isTerminalEquivUnique F X).invFun h⟩ }

/-- We can more explicitly show that a category has an initial object by specifying the object,
and showing there is a unique morphism from it to any other object. -/
theorem has_initial_of_unique (X : C) [h : ∀ Y : C, Unique (X ⟶ Y)] : HasInitial C :=
  { HasColimit := fun F => HasColimit.mk ⟨_, (isInitialEquivUnique F X).invFun h⟩ }

/-- The map from an object to the terminal object. -/
abbrev terminal.from [HasTerminal C] (P : C) : P ⟶ ⊤_ C :=
  limit.lift (Functor.empty C) (asEmptyCone P)

/-- The map to an object from the initial object. -/
abbrev initial.to [HasInitial C] (P : C) : ⊥_ C ⟶ P :=
  colimit.desc (Functor.empty C) (asEmptyCocone P)

/-- A terminal object is terminal. -/
def terminal_is_terminal [HasTerminal C] : IsTerminal (⊤_ C) where
  lift := fun s => terminal.from _

/-- An initial object is initial. -/
def initial_is_initial [HasInitial C] : IsInitial (⊥_ C) where
  desc := fun s => initial.to _

instance unique_to_terminal [HasTerminal C] (P : C) : Unique (P ⟶ ⊤_ C) :=
  isTerminalEquivUnique _ (⊤_ C) terminalIsTerminal P

instance unique_from_initial [HasInitial C] (P : C) : Unique (⊥_ C ⟶ P) :=
  isInitialEquivUnique _ (⊥_ C) initialIsInitial P

@[simp]
theorem terminal.comp_from [HasTerminal C] {P Q : C} (f : P ⟶ Q) : f ≫ terminal.from Q = terminal.from P := by
  tidy

@[simp]
theorem initial.to_comp [HasInitial C] {P Q : C} (f : P ⟶ Q) : initial.to P ≫ f = initial.to Q := by
  tidy

/-- Any morphism from a terminal object is split mono. -/
instance terminal.split_mono_from {Y : C} [HasTerminal C] (f : ⊤_ C ⟶ Y) : SplitMono f :=
  IsTerminal.splitMonoFrom terminalIsTerminal _

/-- Any morphism to an initial object is split epi. -/
instance initial.split_epi_to {Y : C} [HasInitial C] (f : Y ⟶ ⊥_ C) : SplitEpi f :=
  IsInitial.splitEpiTo initialIsInitial _

/-- An initial object is terminal in the opposite category. -/
def terminal_op_of_initial {X : C} (t : IsInitial X) : IsTerminal (Opposite.op X) where
  lift := fun s => (t.to s.x.unop).op
  uniq' := fun s m w => Quiver.Hom.unop_inj (t.hom_ext _ _)

/-- An initial object in the opposite category is terminal in the original category. -/
def terminal_unop_of_initial {X : Cᵒᵖ} (t : IsInitial X) : IsTerminal X.unop where
  lift := fun s => (t.to (Opposite.op s.x)).unop
  uniq' := fun s m w => Quiver.Hom.op_inj (t.hom_ext _ _)

/-- A terminal object is initial in the opposite category. -/
def initial_op_of_terminal {X : C} (t : IsTerminal X) : IsInitial (Opposite.op X) where
  desc := fun s => (t.from s.x.unop).op
  uniq' := fun s m w => Quiver.Hom.unop_inj (t.hom_ext _ _)

/-- A terminal object in the opposite category is initial in the original category. -/
def initial_unop_of_terminal {X : Cᵒᵖ} (t : IsTerminal X) : IsInitial X.unop where
  desc := fun s => (t.from (Opposite.op s.x)).unop
  uniq' := fun s m w => Quiver.Hom.op_inj (t.hom_ext _ _)

/-- A category is a `initial_mono_class` if the canonical morphism of an initial object is a
monomorphism.  In practice, this is most useful when given an arbitrary morphism out of the chosen
initial object, see `initial.mono_from`.
Given a terminal object, this is equivalent to the assumption that the unique morphism from initial
to terminal is a monomorphism, which is the second of Freyd's axioms for an AT category.

TODO: This is a condition satisfied by categories with zero objects and morphisms.
-/
class initial_mono_class (C : Type u₁) [Category.{v₁} C] : Prop where
  is_initial_mono_from : ∀ {I} X : C hI : IsInitial I, Mono (hI.to X)

theorem is_initial.mono_from [InitialMonoClass C] {I} {X : C} (hI : IsInitial I) (f : I ⟶ X) : Mono f := by
  rw [hI.hom_ext f (hI.to X)]
  apply initial_mono_class.is_initial_mono_from

instance (priority := 100) initial.mono_from [HasInitial C] [InitialMonoClass C] (X : C) (f : ⊥_ C ⟶ X) : Mono f :=
  initialIsInitial.mono_from f

/-- To show a category is a `initial_mono_class` it suffices to give an initial object such that
every morphism out of it is a monomorphism. -/
theorem initial_mono_class.of_is_initial {I : C} (hI : IsInitial I) (h : ∀ X, Mono (hI.to X)) : InitialMonoClass C :=
  { is_initial_mono_from := fun I' X hI' => by
      rw [hI'.hom_ext (hI'.to X) ((hI'.unique_up_to_iso hI).Hom ≫ hI.to X)]
      apply mono_comp }

/-- To show a category is a `initial_mono_class` it suffices to show every morphism out of the
initial object is a monomorphism. -/
theorem initial_mono_class.of_initial [HasInitial C] (h : ∀ X : C, Mono (initial.to X)) : InitialMonoClass C :=
  InitialMonoClass.of_is_initial initialIsInitial h

/-- To show a category is a `initial_mono_class` it suffices to show the unique morphism from an
initial object to a terminal object is a monomorphism. -/
theorem initial_mono_class.of_is_terminal {I T : C} (hI : IsInitial I) (hT : IsTerminal T) (f : Mono (hI.to T)) :
    InitialMonoClass C :=
  InitialMonoClass.of_is_initial hI fun X => mono_of_mono_fac (hI.hom_ext (_ ≫ hT.from X) (hI.to T))

/-- To show a category is a `initial_mono_class` it suffices to show the unique morphism from the
initial object to a terminal object is a monomorphism. -/
theorem initial_mono_class.of_terminal [HasInitial C] [HasTerminal C] (h : Mono (initial.to (⊤_ C))) :
    InitialMonoClass C :=
  InitialMonoClass.of_is_terminal initialIsInitial terminalIsTerminal h

section Comparison

variable {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)

/-- The comparison morphism from the image of a terminal object to the terminal object in the target
category.
This is an isomorphism iff `G` preserves terminal objects, see
`category_theory.limits.preserves_terminal.of_iso_comparison`.
-/
def terminal_comparison [HasTerminal C] [HasTerminal D] : G.obj (⊤_ C) ⟶ ⊤_ D :=
  terminal.from _

/-- The comparison morphism from the initial object in the target category to the image of the initial
object.
-/
def initial_comparison [HasInitial C] [HasInitial D] : ⊥_ D ⟶ G.obj (⊥_ C) :=
  initial.to _

end Comparison

variable {J : Type u} [Category.{v} J]

/-- From a functor `F : J ⥤ C`, given an initial object of `J`, construct a cone for `J`.
In `limit_of_diagram_initial` we show it is a limit cone. -/
@[simps]
def cone_of_diagram_initial {X : J} (tX : IsInitial X) (F : J ⥤ C) : Cone F where
  x := F.obj X
  π :=
    { app := fun j => F.map (tX.to j),
      naturality' := fun j j' k => by
        dsimp
        rw [← F.map_comp, category.id_comp, tX.hom_ext (tX.to j ≫ k) (tX.to j')] }

/-- From a functor `F : J ⥤ C`, given an initial object of `J`, show the cone
`cone_of_diagram_initial` is a limit. -/
def limit_of_diagram_initial {X : J} (tX : IsInitial X) (F : J ⥤ C) : IsLimit (coneOfDiagramInitial tX F) where
  lift := fun s => s.π.app X
  uniq' := fun s m w => by
    rw [← w X, cone_of_diagram_initial_π_app, tX.hom_ext (tX.to X) (𝟙 _)]
    dsimp
    simp

/-- For a functor `F : J ⥤ C`, if `J` has an initial object then the image of it is isomorphic
to the limit of `F`. -/
@[reducible]
def limit_of_initial (F : J ⥤ C) [HasInitial J] [HasLimit F] : limit F ≅ F.obj (⊥_ J) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitOfDiagramInitial initialIsInitial F)

/-- From a functor `F : J ⥤ C`, given a terminal object of `J`, construct a cone for `J`,
provided that the morphisms in the diagram are isomorphisms.
In `limit_of_diagram_terminal` we show it is a limit cone. -/
@[simps]
def cone_of_diagram_terminal {X : J} (hX : IsTerminal X) (F : J ⥤ C) [∀ i j : J f : i ⟶ j, IsIso (F.map f)] :
    Cone F where
  x := F.obj X
  π :=
    { app := fun i => inv (F.map (hX.from _)),
      naturality' := by
        intro i j f
        dsimp
        simp only [is_iso.eq_inv_comp, is_iso.comp_inv_eq, category.id_comp, ← F.map_comp,
          hX.hom_ext (hX.from i) (f ≫ hX.from j)] }

/-- From a functor `F : J ⥤ C`, given a terminal object of `J` and that the morphisms in the
diagram are isomorphisms, show the cone `cone_of_diagram_terminal` is a limit. -/
def limit_of_diagram_terminal {X : J} (hX : IsTerminal X) (F : J ⥤ C) [∀ i j : J f : i ⟶ j, IsIso (F.map f)] :
    IsLimit (coneOfDiagramTerminal hX F) where
  lift := fun S => S.π.app _

/-- For a functor `F : J ⥤ C`, if `J` has a terminal object and all the morphisms in the diagram
are isomorphisms, then the image of the terminal object is isomorphic to the limit of `F`. -/
@[reducible]
def limit_of_terminal (F : J ⥤ C) [HasTerminal J] [HasLimit F] [∀ i j : J f : i ⟶ j, IsIso (F.map f)] :
    limit F ≅ F.obj (⊤_ J) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitOfDiagramTerminal terminalIsTerminal F)

/-- From a functor `F : J ⥤ C`, given a terminal object of `J`, construct a cocone for `J`.
In `colimit_of_diagram_terminal` we show it is a colimit cocone. -/
@[simps]
def cocone_of_diagram_terminal {X : J} (tX : IsTerminal X) (F : J ⥤ C) : Cocone F where
  x := F.obj X
  ι :=
    { app := fun j => F.map (tX.from j),
      naturality' := fun j j' k => by
        dsimp
        rw [← F.map_comp, category.comp_id, tX.hom_ext (k ≫ tX.from j') (tX.from j)] }

/-- From a functor `F : J ⥤ C`, given a terminal object of `J`, show the cocone
`cocone_of_diagram_terminal` is a colimit. -/
def colimit_of_diagram_terminal {X : J} (tX : IsTerminal X) (F : J ⥤ C) : IsColimit (coconeOfDiagramTerminal tX F) where
  desc := fun s => s.ι.app X
  uniq' := fun s m w => by
    rw [← w X, cocone_of_diagram_terminal_ι_app, tX.hom_ext (tX.from X) (𝟙 _)]
    simp

/-- For a functor `F : J ⥤ C`, if `J` has a terminal object then the image of it is isomorphic
to the colimit of `F`. -/
@[reducible]
def colimit_of_terminal (F : J ⥤ C) [HasTerminal J] [HasColimit F] : colimit F ≅ F.obj (⊤_ J) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (colimitOfDiagramTerminal terminalIsTerminal F)

/-- From a functor `F : J ⥤ C`, given an initial object of `J`, construct a cocone for `J`,
provided that the morphisms in the diagram are isomorphisms.
In `colimit_of_diagram_initial` we show it is a colimit cocone. -/
@[simps]
def cocone_of_diagram_initial {X : J} (hX : IsInitial X) (F : J ⥤ C) [∀ i j : J f : i ⟶ j, IsIso (F.map f)] :
    Cocone F where
  x := F.obj X
  ι :=
    { app := fun i => inv (F.map (hX.to _)),
      naturality' := by
        intro i j f
        dsimp
        simp only [is_iso.eq_inv_comp, is_iso.comp_inv_eq, category.comp_id, ← F.map_comp,
          hX.hom_ext (hX.to i ≫ f) (hX.to j)] }

/-- From a functor `F : J ⥤ C`, given an initial object of `J` and that the morphisms in the
diagram are isomorphisms, show the cone `cocone_of_diagram_initial` is a colimit. -/
def colimit_of_diagram_initial {X : J} (hX : IsInitial X) (F : J ⥤ C) [∀ i j : J f : i ⟶ j, IsIso (F.map f)] :
    IsColimit (coconeOfDiagramInitial hX F) where
  desc := fun S => S.ι.app _

/-- For a functor `F : J ⥤ C`, if `J` has an initial object and all the morphisms in the diagram
are isomorphisms, then the image of the initial object is isomorphic to the colimit of `F`. -/
@[reducible]
def colimit_of_initial (F : J ⥤ C) [HasInitial J] [HasColimit F] [∀ i j : J f : i ⟶ j, IsIso (F.map f)] :
    colimit F ≅ F.obj (⊥_ J) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (colimitOfDiagramInitial initialIsInitial _)

/-- If `j` is initial in the index category, then the map `limit.π F j` is an isomorphism.
-/
theorem is_iso_π_of_is_initial {j : J} (I : IsInitial j) (F : J ⥤ C) [HasLimit F] : IsIso (limit.π F j) :=
  ⟨⟨limit.lift _ (coneOfDiagramInitial I F),
      ⟨by
        ext
        simp , by
        simp ⟩⟩⟩

instance is_iso_π_initial [HasInitial J] (F : J ⥤ C) [HasLimit F] : IsIso (limit.π F (⊥_ J)) :=
  is_iso_π_of_is_initial initialIsInitial F

theorem is_iso_π_of_is_terminal {j : J} (I : IsTerminal j) (F : J ⥤ C) [HasLimit F]
    [∀ i j : J f : i ⟶ j, IsIso (F.map f)] : IsIso (limit.π F j) :=
  ⟨⟨limit.lift _ (coneOfDiagramTerminal I F), by
      ext
      simp , by
      simp ⟩⟩

instance is_iso_π_terminal [HasTerminal J] (F : J ⥤ C) [HasLimit F] [∀ i j : J f : i ⟶ j, IsIso (F.map f)] :
    IsIso (limit.π F (⊤_ J)) :=
  is_iso_π_of_is_terminal terminalIsTerminal F

/-- If `j` is terminal in the index category, then the map `colimit.ι F j` is an isomorphism.
-/
theorem is_iso_ι_of_is_terminal {j : J} (I : IsTerminal j) (F : J ⥤ C) [HasColimit F] : IsIso (colimit.ι F j) :=
  ⟨⟨colimit.desc _ (coconeOfDiagramTerminal I F),
      ⟨by
        simp , by
        ext
        simp ⟩⟩⟩

instance is_iso_ι_terminal [HasTerminal J] (F : J ⥤ C) [HasColimit F] : IsIso (colimit.ι F (⊤_ J)) :=
  is_iso_ι_of_is_terminal terminalIsTerminal F

theorem is_iso_ι_of_is_initial {j : J} (I : IsInitial j) (F : J ⥤ C) [HasColimit F]
    [∀ i j : J f : i ⟶ j, IsIso (F.map f)] : IsIso (colimit.ι F j) :=
  ⟨⟨colimit.desc _ (coconeOfDiagramInitial I F),
      ⟨by
        tidy, by
        ext
        simp ⟩⟩⟩

instance is_iso_ι_initial [HasInitial J] (F : J ⥤ C) [HasColimit F] [∀ i j : J f : i ⟶ j, IsIso (F.map f)] :
    IsIso (colimit.ι F (⊥_ J)) :=
  is_iso_ι_of_is_initial initialIsInitial F

end

end CategoryTheory.Limits

