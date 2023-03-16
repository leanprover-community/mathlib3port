/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.connected_components
! leanprover-community/mathlib commit 10bf4f825ad729c5653adc039dafa3622e7f93c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Chain
import Mathbin.CategoryTheory.IsConnected
import Mathbin.CategoryTheory.Sigma.Basic
import Mathbin.CategoryTheory.FullSubcategory

/-!
# Connected components of a category

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Defines a type `connected_components J` indexing the connected components of a category, and the
full subcategories giving each connected component: `component j : Type u₁`.
We show that each `component j` is in fact connected.

We show every category can be expressed as a disjoint union of its connected components, in
particular `decomposed J` is the category (definitionally) given by the sigma-type of the connected
components of `J`, and it is shown that this is equivalent to `J`.
-/


universe v₁ v₂ v₃ u₁ u₂

noncomputable section

open CategoryTheory.Category

namespace CategoryTheory

attribute [instance] is_connected.is_nonempty

variable {J : Type u₁} [Category.{v₁} J]

variable {C : Type u₂} [Category.{u₁} C]

#print CategoryTheory.ConnectedComponents /-
/-- This type indexes the connected components of the category `J`. -/
def ConnectedComponents (J : Type u₁) [Category.{v₁} J] : Type u₁ :=
  Quotient (Zigzag.setoid J)
#align category_theory.connected_components CategoryTheory.ConnectedComponents
-/

instance [Inhabited J] : Inhabited (ConnectedComponents J) :=
  ⟨Quotient.mk'' default⟩

#print CategoryTheory.Component /-
/-- Given an index for a connected component, produce the actual component as a full subcategory. -/
def Component (j : ConnectedComponents J) : Type u₁ :=
  FullSubcategory fun k => Quotient.mk'' k = j deriving Category
#align category_theory.component CategoryTheory.Component
-/

/- warning: category_theory.component.ι -> CategoryTheory.Component.ι is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] (j : CategoryTheory.ConnectedComponents.{u1, u2} J _inst_1), CategoryTheory.Functor.{u1, u1, u2, u2} (CategoryTheory.Component.{u1, u2} J _inst_1 j) (CategoryTheory.InducedCategory.category.{u1, u2, u2} (CategoryTheory.FullSubcategoryₓ.{u1, u2} J _inst_1 (fun (k : J) => Eq.{succ u2} (Quotient.{succ u2} J (CategoryTheory.Zigzag.setoid.{u1, u2} J _inst_1)) (Quotient.mk''.{succ u2} J (CategoryTheory.Zigzag.setoid.{u1, u2} J _inst_1) k) j)) J _inst_1 (CategoryTheory.FullSubcategoryₓ.obj.{u1, u2} J _inst_1 (fun (k : J) => Eq.{succ u2} (Quotient.{succ u2} J (CategoryTheory.Zigzag.setoid.{u1, u2} J _inst_1)) (Quotient.mk''.{succ u2} J (CategoryTheory.Zigzag.setoid.{u1, u2} J _inst_1) k) j))) J _inst_1
but is expected to have type
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] (j : CategoryTheory.ConnectedComponents.{u1, u2} J _inst_1), CategoryTheory.Functor.{u1, u1, u2, u2} (CategoryTheory.Component.{u1, u2} J _inst_1 j) (CategoryTheory.instCategoryComponent.{u1, u2} J _inst_1 j) J _inst_1
Case conversion may be inaccurate. Consider using '#align category_theory.component.ι CategoryTheory.Component.ιₓ'. -/
/-- The inclusion functor from a connected component to the whole category. -/
@[simps (config := { rhsMd := semireducible })]
def Component.ι (j) : Component j ⥤ J :=
  fullSubcategoryInclusion _ deriving Full, Faithful
#align category_theory.component.ι CategoryTheory.Component.ι

/-- Each connected component of the category is nonempty. -/
instance (j : ConnectedComponents J) : Nonempty (Component j) :=
  by
  apply Quotient.inductionOn' j
  intro k
  refine' ⟨⟨k, rfl⟩⟩

instance (j : ConnectedComponents J) : Inhabited (Component j) :=
  Classical.inhabited_of_nonempty'

/-- Each connected component of the category is connected. -/
instance (j : ConnectedComponents J) : IsConnected (Component j) :=
  by
  -- Show it's connected by constructing a zigzag (in `component j`) between any two objects
  apply is_connected_of_zigzag
  rintro ⟨j₁, hj₁⟩ ⟨j₂, rfl⟩
  -- We know that the underlying objects j₁ j₂ have some zigzag between them in `J`
  have h₁₂ : zigzag j₁ j₂ := Quotient.exact' hj₁
  -- Get an explicit zigzag as a list
  rcases List.exists_chain_of_relationReflTransGen h₁₂ with ⟨l, hl₁, hl₂⟩
  -- Everything which has a zigzag to j₂ can be lifted to the same component as `j₂`.
  let f : ∀ x, zigzag x j₂ → component (Quotient.mk'' j₂) := fun x h => ⟨x, Quotient.sound' h⟩
  -- Everything in our chosen zigzag from `j₁` to `j₂` has a zigzag to `j₂`.
  have hf : ∀ a : J, a ∈ l → zigzag a j₂ := by
    intro i hi
    apply List.Chain.induction (fun t => zigzag t j₂) _ hl₁ hl₂ _ _ _ (Or.inr hi)
    · intro j k
      apply Relation.ReflTransGen.head
    · apply Relation.ReflTransGen.refl
  -- Now lift the zigzag from `j₁` to `j₂` in `J` to the same thing in `component j`.
  refine' ⟨l.pmap f hf, _, _⟩
  · refine' @List.chain_pmap_of_chain _ _ _ f (fun x y _ _ h => _) hl₁ h₁₂ _
    exact zag_of_zag_obj (component.ι _) h
  · erw [List.getLast_pmap _ f (j₁ :: l) (by simpa [h₁₂] using hf) (List.cons_ne_nil _ _)]
    exact full_subcategory.ext _ _ hl₂

#print CategoryTheory.Decomposed /-
/-- The disjoint union of `J`s connected components, written explicitly as a sigma-type with the
category structure.
This category is equivalent to `J`.
-/
abbrev Decomposed (J : Type u₁) [Category.{v₁} J] :=
  Σj : ConnectedComponents J, Component j
#align category_theory.decomposed CategoryTheory.Decomposed
-/

#print CategoryTheory.inclusion /-
-- This name may cause clashes further down the road, and so might need to be changed.
/--
The inclusion of each component into the decomposed category. This is just `sigma.incl` but having
this abbreviation helps guide typeclass search to get the right category instance on `decomposed J`.
-/
abbrev inclusion (j : ConnectedComponents J) : Component j ⥤ Decomposed J :=
  Sigma.incl _
#align category_theory.inclusion CategoryTheory.inclusion
-/

#print CategoryTheory.decomposedTo /-
/-- The forward direction of the equivalence between the decomposed category and the original. -/
@[simps (config := { rhsMd := semireducible })]
def decomposedTo (J : Type u₁) [Category.{v₁} J] : Decomposed J ⥤ J :=
  Sigma.desc Component.ι
#align category_theory.decomposed_to CategoryTheory.decomposedTo
-/

#print CategoryTheory.inclusion_comp_decomposedTo /-
@[simp]
theorem inclusion_comp_decomposedTo (j : ConnectedComponents J) :
    inclusion j ⋙ decomposedTo J = Component.ι j :=
  rfl
#align category_theory.inclusion_comp_decomposed_to CategoryTheory.inclusion_comp_decomposedTo
-/

instance : Full (decomposedTo J)
    where
  Preimage := by
    rintro ⟨j', X, hX⟩ ⟨k', Y, hY⟩ f
    dsimp at f
    have : j' = k'
    rw [← hX, ← hY, Quotient.eq'']
    exact Relation.ReflTransGen.single (Or.inl ⟨f⟩)
    subst this
    refine' sigma.sigma_hom.mk f
  witness' := by
    rintro ⟨j', X, hX⟩ ⟨_, Y, rfl⟩ f
    have : Quotient.mk'' Y = j' := by
      rw [← hX, Quotient.eq'']
      exact Relation.ReflTransGen.single (Or.inr ⟨f⟩)
    subst this
    rfl

instance : Faithful (decomposedTo J)
    where map_injective' := by
    rintro ⟨_, j, rfl⟩ ⟨_, k, hY⟩ ⟨f⟩ ⟨g⟩ e
    change f = g at e
    subst e

instance : EssSurj (decomposedTo J) where mem_essImage j := ⟨⟨_, j, rfl⟩, ⟨Iso.refl _⟩⟩

instance : IsEquivalence (decomposedTo J) :=
  Equivalence.ofFullyFaithfullyEssSurj _

/- warning: category_theory.decomposed_equiv -> CategoryTheory.decomposedEquiv is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J], CategoryTheory.Equivalence.{max u1 u2, u1, u2, u2} (CategoryTheory.Decomposed.{u1, u2} J _inst_1) (CategoryTheory.Sigma.sigma.{u2, u1, u2} (CategoryTheory.ConnectedComponents.{u1, u2} J _inst_1) (fun (j : CategoryTheory.ConnectedComponents.{u1, u2} J _inst_1) => CategoryTheory.Component.{u1, u2} J _inst_1 j) (fun (i : CategoryTheory.ConnectedComponents.{u1, u2} J _inst_1) => CategoryTheory.Component.category.{u2, u1} J _inst_1 i)) J _inst_1
but is expected to have type
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J], CategoryTheory.Equivalence.{max u2 u1, u1, u2, u2} (CategoryTheory.Decomposed.{u1, u2} J _inst_1) J (CategoryTheory.Sigma.sigma.{u2, u1, u2} (CategoryTheory.ConnectedComponents.{u1, u2} J _inst_1) (fun (j : CategoryTheory.ConnectedComponents.{u1, u2} J _inst_1) => CategoryTheory.Component.{u1, u2} J _inst_1 j) (fun (i : CategoryTheory.ConnectedComponents.{u1, u2} J _inst_1) => CategoryTheory.instCategoryComponent.{u1, u2} J _inst_1 i)) _inst_1
Case conversion may be inaccurate. Consider using '#align category_theory.decomposed_equiv CategoryTheory.decomposedEquivₓ'. -/
/-- This gives that any category is equivalent to a disjoint union of connected categories. -/
@[simps (config := { rhsMd := semireducible }) Functor]
def decomposedEquiv : Decomposed J ≌ J :=
  (decomposedTo J).asEquivalence
#align category_theory.decomposed_equiv CategoryTheory.decomposedEquiv

end CategoryTheory

