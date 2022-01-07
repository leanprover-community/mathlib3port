import Mathbin.CategoryTheory.Limits.Cones
import Mathbin.CategoryTheory.StructuredArrow
import Mathbin.CategoryTheory.FinCategory

/-!
# Bicones

Given a category `J`, a walking `bicone J` is a category whose objects are the objects of `J` and
two extra vertices `bicone.left` and `bicone.right`. The morphisms are the morphisms of `J` and
`left ⟶ j`, `right ⟶ j` for each `j : J` such that `⬝ ⟶ j` and `⬝ ⟶ k` commutes with each
`f : j ⟶ k`.

Given a diagram `F : J ⥤ C` and two `cone F`s, we can join them into a diagram `bicone J ⥤ C` via
`bicone_mk`.

This is used in `category_theory.flat_functors.preserves_finite_limits_of_flat`.
-/


universe v₁ u₁

open CategoryTheory.Limits

namespace CategoryTheory

section Bicone

variable (J : Type u₁)

/-- Given a category `J`, construct a walking `bicone J` by adjoining two elements. -/
inductive bicone
  | left : bicone
  | right : bicone
  | diagram (val : J) : bicone
  deriving DecidableEq

instance : Inhabited (bicone J) :=
  ⟨bicone.left⟩

instance fin_bicone [Fintype J] [DecidableEq J] : Fintype (bicone J) where
  elems := [bicone.left, bicone.right].toFinset ∪ Finset.image bicone.diagram (Fintype.elems J)
  complete := fun j => by
    cases j <;> simp
    exact Fintype.complete j

variable [category.{v₁} J] [∀ j k : J, DecidableEq (j ⟶ k)]

/-- The homs for a walking `bicone J`. -/
inductive bicone_hom : bicone J → bicone J → Type max u₁ v₁
  | left_id : bicone_hom bicone.left bicone.left
  | right_id : bicone_hom bicone.right bicone.right
  | left (j : J) : bicone_hom bicone.left (bicone.diagram j)
  | right (j : J) : bicone_hom bicone.right (bicone.diagram j)
  | diagram {j k : J} (f : j ⟶ k) : bicone_hom (bicone.diagram j) (bicone.diagram k)

instance : Inhabited (bicone_hom J bicone.left bicone.left) :=
  ⟨bicone_hom.left_id⟩

instance bicone_hom.decidable_eq {j k : bicone J} : DecidableEq (bicone_hom J j k) := fun f g => by
  cases f <;> cases g <;> simp <;> infer_instance

@[simps]
instance bicone_category_struct : category_struct (bicone J) where
  Hom := bicone_hom J
  id := fun j => bicone.cases_on j bicone_hom.left_id bicone_hom.right_id fun k => bicone_hom.diagram (𝟙 k)
  comp := fun X Y Z f g => by
    cases f
    exact g
    exact g
    cases g
    exact bicone_hom.left g_k
    cases g
    exact bicone_hom.right g_k
    cases g
    exact bicone_hom.diagram (f_f ≫ g_f)

instance bicone_category : category (bicone J) where
  id_comp' := fun X Y f => by
    cases f <;> simp
  comp_id' := fun X Y f => by
    cases f <;> simp
  assoc' := fun W X Y Z f g h => by
    cases f <;> cases g <;> cases h <;> simp

end Bicone

section SmallCategory

variable (J : Type v₁) [small_category J]

/-- Given a diagram `F : J ⥤ C` and two `cone F`s, we can join them into a diagram `bicone J ⥤ C`.
-/
@[simps]
def bicone_mk [∀ j k : J, DecidableEq (j ⟶ k)] {C : Type u₁} [category.{v₁} C] {F : J ⥤ C} (c₁ c₂ : cone F) :
    bicone J ⥤ C where
  obj := fun X => bicone.cases_on X c₁.X c₂.X fun j => F.obj j
  map := fun X Y f => by
    cases f
    exact 𝟙 _
    exact 𝟙 _
    exact c₁.π.app f_1
    exact c₂.π.app f_1
    exact F.map f_f
  map_id' := fun X => by
    cases X <;> simp
  map_comp' := fun X Y Z f g => by
    cases f
    exact (category.id_comp _).symm
    exact (category.id_comp _).symm
    cases g
    exact (category.id_comp _).symm.trans (c₁.π.naturality g_f : _)
    cases g
    exact (category.id_comp _).symm.trans (c₂.π.naturality g_f : _)
    cases g
    exact F.map_comp _ _

instance fin_bicone_hom [fin_category J] (j k : bicone J) : Fintype (j ⟶ k) := by
  cases j <;> cases k
  exact
    { elems := {bicone_hom.left_id},
      complete := fun f => by
        cases f
        simp }
  exact
    { elems := ∅,
      complete := fun f => by
        cases f }
  exact
    { elems := {bicone_hom.left k},
      complete := fun f => by
        cases f
        simp }
  exact
    { elems := ∅,
      complete := fun f => by
        cases f }
  exact
    { elems := {bicone_hom.right_id},
      complete := fun f => by
        cases f
        simp }
  exact
    { elems := {bicone_hom.right k},
      complete := fun f => by
        cases f
        simp }
  exact
    { elems := ∅,
      complete := fun f => by
        cases f }
  exact
    { elems := ∅,
      complete := fun f => by
        cases f }
  exact
    { elems := Finset.image bicone_hom.diagram (Fintype.elems (j ⟶ k)),
      complete := fun f => by
        cases f
        simp only [Finset.mem_image]
        use f_f
        simpa using Fintype.complete _ }

instance bicone_small_category [∀ j k : J, DecidableEq (j ⟶ k)] : small_category (bicone J) :=
  CategoryTheory.biconeCategory J

instance bicone_fin_category [fin_category J] : fin_category (bicone J) :=
  {  }

end SmallCategory

end CategoryTheory

