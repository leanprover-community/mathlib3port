/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison
-/
import Mathbin.Tactic.ReassocAxiom
import Mathbin.Tactic.Monotonicity.Default
import Mathbin.CategoryTheory.Category.Basic

/-!
# Functors

Defines a functor between categories, extending a `prefunctor` between quivers.

Introduces notation `C ⥤ D` for the type of all functors from `C` to `D`.
(Unfortunately the `⇒` arrow (`\functor`) is taken by core, 
but in mathlib4 we should switch to this.)
-/


namespace CategoryTheory

-- declare the `v`'s first; see `category_theory.category` for an explanation
universe v v₁ v₂ v₃ u u₁ u₂ u₃

section

/-- `functor C D` represents a functor between categories `C` and `D`.

To apply a functor `F` to an object use `F.obj X`, and to a morphism use `F.map f`.

The axiom `map_id` expresses preservation of identities, and
`map_comp` expresses functoriality.

See https://stacks.math.columbia.edu/tag/001B.
-/
structure Functor (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] extends Prefunctor C D :
  Type max v₁ v₂ u₁ u₂ where
  map_id' : ∀ X : C, map (𝟙 X) = 𝟙 (obj X) := by
    run_tac
      obviously
  map_comp' : ∀ {X Y Z : C} f : X ⟶ Y g : Y ⟶ Z, map (f ≫ g) = map f ≫ map g := by
    run_tac
      obviously

/-- The prefunctor between the underlying quivers. -/
add_decl_doc functor.to_prefunctor

end

-- mathport name: «expr ⥤ »
infixr:26
  " ⥤ " =>-- A functor is basically a function, so give ⥤ a similar precedence to → (25).
  -- For example, `C × D ⥤ E` should parse as `(C × D) ⥤ E` not `C × (D ⥤ E)`.
  Functor

-- type as \func --
restate_axiom functor.map_id'

attribute [simp] Functor.map_id

restate_axiom functor.map_comp'

attribute [reassoc, simp] functor.map_comp

namespace Functor

section

variable (C : Type u₁) [Category.{v₁} C]

/-- `𝟭 C` is the identity functor on a category `C`. -/
protected def id : C ⥤ C where
  obj := fun X => X
  map := fun _ _ f => f

-- mathport name: «expr𝟭»
notation "𝟭" => Functor.id

-- Type this as `\sb1`
instance : Inhabited (C ⥤ C) :=
  ⟨Functor.id C⟩

variable {C}

@[simp]
theorem id_obj (X : C) : (𝟭 C).obj X = X :=
  rfl

@[simp]
theorem id_map {X Y : C} (f : X ⟶ Y) : (𝟭 C).map f = f :=
  rfl

end

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]

/-- `F ⋙ G` is the composition of a functor `F` and a functor `G` (`F` first, then `G`).
-/
def comp (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E where
  obj := fun X => G.obj (F.obj X)
  map := fun _ _ f => G.map (F.map f)

-- mathport name: «expr ⋙ »
infixr:80 " ⋙ " => comp

@[simp]
theorem comp_obj (F : C ⥤ D) (G : D ⥤ E) (X : C) : (F ⋙ G).obj X = G.obj (F.obj X) :=
  rfl

@[simp]
theorem comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y : C} (f : X ⟶ Y) : (F ⋙ G).map f = G.map (F.map f) :=
  rfl

-- These are not simp lemmas because rewriting along equalities between functors
-- is not necessarily a good idea.
-- Natural isomorphisms are also provided in `whiskering.lean`.
protected theorem comp_id (F : C ⥤ D) : F ⋙ 𝟭 D = F := by
  cases F <;> rfl

protected theorem id_comp (F : C ⥤ D) : 𝟭 C ⋙ F = F := by
  cases F <;> rfl

@[simp]
theorem map_dite (F : C ⥤ D) {X Y : C} {P : Prop} [Decidable P] (f : P → (X ⟶ Y)) (g : ¬P → (X ⟶ Y)) :
    F.map (if h : P then f h else g h) = if h : P then F.map (f h) else F.map (g h) := by
  split_ifs <;> rfl

end

end Functor

end CategoryTheory

