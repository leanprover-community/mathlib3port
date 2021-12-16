import Mathbin.Data.List.Chain 
import Mathbin.CategoryTheory.Punit 
import Mathbin.CategoryTheory.IsConnected 
import Mathbin.CategoryTheory.Sigma.Basic 
import Mathbin.CategoryTheory.FullSubcategory

/-!
# Connected components of a category

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

variable {J : Type u₁} [category.{v₁} J]

variable {C : Type u₂} [category.{u₁} C]

/-- This type indexes the connected components of the category `J`. -/
def connected_components (J : Type u₁) [category.{v₁} J] : Type u₁ :=
  Quotientₓ (zigzag.setoid J)

instance [Inhabited J] : Inhabited (connected_components J) :=
  ⟨Quotientₓ.mk' (default J)⟩

-- ././Mathport/Syntax/Translate/Basic.lean:748:9: unsupported derive handler category
/-- Given an index for a connected component, produce the actual component as a full subcategory. -/
def component (j : connected_components J) : Type u₁ :=
  { k : J // Quotientₓ.mk' k = j }deriving [anonymous]

-- ././Mathport/Syntax/Translate/Basic.lean:748:9: unsupported derive handler full
-- ././Mathport/Syntax/Translate/Basic.lean:748:9: unsupported derive handler faithful
/-- The inclusion functor from a connected component to the whole category. -/
@[simps (config := { rhsMd := semireducible })]
def component.ι j : component j ⥤ J :=
  full_subcategory_inclusion _ deriving [anonymous], [anonymous]

/-- Each connected component of the category is nonempty. -/
instance (j : connected_components J) : Nonempty (component j) :=
  by 
    apply Quotientₓ.induction_on' j 
    intro k 
    refine' ⟨⟨k, rfl⟩⟩

instance (j : connected_components J) : Inhabited (component j) :=
  Classical.inhabitedOfNonempty'

/-- Each connected component of the category is connected. -/
instance (j : connected_components J) : is_connected (component j) :=
  by 
    apply is_connected_of_zigzag 
    rintro ⟨j₁, hj₁⟩ ⟨j₂, rfl⟩
    have h₁₂ : zigzag j₁ j₂ := Quotientₓ.exact' hj₁ 
    rcases List.exists_chain_of_relation_refl_trans_gen h₁₂ with ⟨l, hl₁, hl₂⟩
    let f : ∀ x, zigzag x j₂ → component (Quotientₓ.mk' j₂) := fun x h => ⟨x, Quotientₓ.sound' h⟩
    have hf : ∀ a : J, a ∈ l → zigzag a j₂
    ·
      intro i hi 
      apply List.Chain.induction (fun t => zigzag t j₂) _ hl₁ hl₂ _ _ _ (Or.inr hi)
      ·
        intro j k 
        apply Relation.ReflTransGen.head
      ·
        apply Relation.ReflTransGen.refl 
    refine' ⟨l.pmap f hf, _, _⟩
    ·
      refine' @List.chain_pmap_of_chain _ _ _ f (fun x y _ _ h => _) hl₁ h₁₂ _ 
      exact zag_of_zag_obj (component.ι _) h
    ·
      erw
        [List.last_pmap _ f (j₁ :: l)
          (by 
            simpa [h₁₂] using hf)
          (List.cons_ne_nil _ _)]
      exact Subtype.ext hl₂

/--
The disjoint union of `J`s connected components, written explicitly as a sigma-type with the
category structure.
This category is equivalent to `J`.
-/
abbrev decomposed (J : Type u₁) [category.{v₁} J] :=
  Σ j : connected_components J, component j

/--
The inclusion of each component into the decomposed category. This is just `sigma.incl` but having
this abbreviation helps guide typeclass search to get the right category instance on `decomposed J`.
-/
abbrev inclusion (j : connected_components J) : component j ⥤ decomposed J :=
  sigma.incl _

/-- The forward direction of the equivalence between the decomposed category and the original. -/
@[simps (config := { rhsMd := semireducible })]
def decomposed_to (J : Type u₁) [category.{v₁} J] : decomposed J ⥤ J :=
  sigma.desc component.ι

@[simp]
theorem inclusion_comp_decomposed_to (j : connected_components J) : inclusion j ⋙ decomposed_to J = component.ι j :=
  rfl

instance : full (decomposed_to J) :=
  { Preimage :=
      by 
        rintro ⟨j', X, hX⟩ ⟨k', Y, hY⟩ f 
        dsimp  at f 
        have  : j' = k' 
        rw [←hX, ←hY, Quotientₓ.eq']
        exact Relation.ReflTransGen.single (Or.inl ⟨f⟩)
        subst this 
        refine' sigma.sigma_hom.mk f,
    witness' :=
      by 
        rintro ⟨j', X, hX⟩ ⟨_, Y, rfl⟩ f 
        have  : Quotientₓ.mk' Y = j'
        ·
          rw [←hX, Quotientₓ.eq']
          exact Relation.ReflTransGen.single (Or.inr ⟨f⟩)
        subst this 
        rfl }

instance : faithful (decomposed_to J) :=
  { map_injective' :=
      by 
        rintro ⟨_, j, rfl⟩ ⟨_, k, hY⟩ ⟨_, _, _, f⟩ ⟨_, _, _, g⟩ e 
        change f = g at e 
        subst e }

instance : ess_surj (decomposed_to J) :=
  { mem_ess_image := fun j => ⟨⟨_, j, rfl⟩, ⟨iso.refl _⟩⟩ }

instance : is_equivalence (decomposed_to J) :=
  equivalence.of_fully_faithfully_ess_surj _

/-- This gives that any category is equivalent to a disjoint union of connected categories. -/
@[simps (config := { rhsMd := semireducible }) Functor]
def decomposed_equiv : decomposed J ≌ J :=
  (decomposed_to J).asEquivalence

end CategoryTheory

