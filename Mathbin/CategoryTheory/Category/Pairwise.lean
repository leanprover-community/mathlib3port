import Mathbin.CategoryTheory.Category.Preorder
import Mathbin.CategoryTheory.Limits.IsLimit

/-!
# The category of "pairwise intersections".

Given `ι : Type v`, we build the diagram category `pairwise ι`
with objects `single i` and `pair i j`, for `i j : ι`,
whose only non-identity morphisms are
`left : pair i j ⟶ single i` and `right : pair i j ⟶ single j`.

We use this later in describing (one formulation of) the sheaf condition.

Given any function `U : ι → α`, where `α` is some complete lattice (e.g. `(opens X)ᵒᵖ`),
we produce a functor `pairwise ι ⥤ α` in the obvious way,
and show that `supr U` provides a colimit cocone over this functor.
-/


noncomputable section

universe v u

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory

/-- An inductive type representing either a single term of a type `ι`, or a pair of terms.
We use this as the objects of a category to describe the sheaf condition.
-/
inductive Pairwise (ι : Type v)
  | single : ι → Pairwise
  | pair : ι → ι → Pairwise

variable {ι : Type v}

namespace Pairwise

instance pairwise_inhabited [Inhabited ι] : Inhabited (Pairwise ι) :=
  ⟨single (default ι)⟩

/-- Morphisms in the category `pairwise ι`. The only non-identity morphisms are
`left i j : single i ⟶ pair i j` and `right i j : single j ⟶ pair i j`.
-/
inductive hom : Pairwise ι → Pairwise ι → Type v
  | id_single : ∀ i, hom (single i) (single i)
  | id_pair : ∀ i j, hom (pair i j) (pair i j)
  | left : ∀ i j, hom (pair i j) (single i)
  | right : ∀ i j, hom (pair i j) (single j)

open Hom

instance hom_inhabited [Inhabited ι] : Inhabited (hom (single (default ι)) (single (default ι))) :=
  ⟨id_single (default ι)⟩

/-- The identity morphism in `pairwise ι`.
-/
def id : ∀ o : Pairwise ι, hom o o
  | single i => id_single i
  | pair i j => id_pair i j

/-- Composition of morphisms in `pairwise ι`. -/
def comp : ∀ {o₁ o₂ o₃ : Pairwise ι} f : hom o₁ o₂ g : hom o₂ o₃, hom o₁ o₃
  | _, _, _, id_single i, g => g
  | _, _, _, id_pair i j, g => g
  | _, _, _, left i j, id_single _ => left i j
  | _, _, _, right i j, id_single _ => right i j

section

attribute [local tidy] tactic.case_bash

instance : category (Pairwise ι) where
  Hom := hom
  id := id
  comp := fun X Y Z f g => comp f g

end

variable {α : Type v} (U : ι → α)

section

variable [SemilatticeInf α]

/-- Auxiliary definition for `diagram`. -/
@[simp]
def diagram_obj : Pairwise ι → α
  | single i => U i
  | pair i j => U i⊓U j

/-- Auxiliary definition for `diagram`. -/
@[simp]
def diagram_map : ∀ {o₁ o₂ : Pairwise ι} f : o₁ ⟶ o₂, diagram_obj U o₁ ⟶ diagram_obj U o₂
  | _, _, id_single i => 𝟙 _
  | _, _, id_pair i j => 𝟙 _
  | _, _, left i j => hom_of_le inf_le_left
  | _, _, right i j => hom_of_le inf_le_right

/-- Given a function `U : ι → α` for `[semilattice_inf α]`, we obtain a functor `pairwise ι ⥤ α`,
sending `single i` to `U i` and `pair i j` to `U i ⊓ U j`,
and the morphisms to the obvious inequalities.
-/
@[simps]
def diagram : Pairwise ι ⥤ α where
  obj := diagram_obj U
  map := fun X Y f => diagram_map U f

end

section

variable [CompleteLattice α]

/-- Auxiliary definition for `cocone`. -/
def cocone_ι_app : ∀ o : Pairwise ι, diagram_obj U o ⟶ supr U
  | single i => hom_of_le (le_supr U i)
  | pair i j => hom_of_le inf_le_left ≫ hom_of_le (le_supr U i)

/-- Given a function `U : ι → α` for `[complete_lattice α]`,
`supr U` provides a cocone over `diagram U`.
-/
@[simps]
def cocone : cocone (diagram U) where
  x := supr U
  ι := { app := cocone_ι_app U }

/-- Given a function `U : ι → α` for `[complete_lattice α]`,
`infi U` provides a limit cone over `diagram U`.
-/
def cocone_is_colimit : is_colimit (cocone U) where
  desc := fun s =>
    hom_of_le
      (by
        apply CompleteLattice.Sup_le
        rintro _ ⟨j, rfl⟩
        exact (s.ι.app (single j)).le)

end

end Pairwise

end CategoryTheory

