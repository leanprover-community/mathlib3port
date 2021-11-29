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

noncomputable theory

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

-- error in CategoryTheory.ConnectedComponents: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler category
/-- Given an index for a connected component, produce the actual component as a full subcategory. -/
@[derive #[expr category]]
def component (j : connected_components J) : Type u₁ :=
{k : J // «expr = »(quotient.mk' k, j)}

-- error in CategoryTheory.ConnectedComponents: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler full
/-- The inclusion functor from a connected component to the whole category. -/
@[derive #["[", expr full, ",", expr faithful, "]"], simps #[expr { rhs_md := semireducible }]]
def component.ι (j) : «expr ⥤ »(component j, J) :=
full_subcategory_inclusion _

/-- Each connected component of the category is nonempty. -/
instance (j : connected_components J) : Nonempty (component j) :=
  by 
    apply Quotientₓ.induction_on' j 
    intro k 
    refine' ⟨⟨k, rfl⟩⟩

instance (j : connected_components J) : Inhabited (component j) :=
  Classical.inhabitedOfNonempty'

-- error in CategoryTheory.ConnectedComponents: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Each connected component of the category is connected. -/
instance (j : connected_components J) : is_connected (component j) :=
begin
  apply [expr is_connected_of_zigzag],
  rintro ["⟨", ident j₁, ",", ident hj₁, "⟩", "⟨", ident j₂, ",", ident rfl, "⟩"],
  have [ident h₁₂] [":", expr zigzag j₁ j₂] [":=", expr quotient.exact' hj₁],
  rcases [expr list.exists_chain_of_relation_refl_trans_gen h₁₂, "with", "⟨", ident l, ",", ident hl₁, ",", ident hl₂, "⟩"],
  let [ident f] [":", expr ∀ x, zigzag x j₂ → component (quotient.mk' j₂)] [":=", expr λ x h, ⟨x, quotient.sound' h⟩],
  have [ident hf] [":", expr ∀ a : J, «expr ∈ »(a, l) → zigzag a j₂] [],
  { intros [ident i, ident hi],
    apply [expr list.chain.induction (λ t, zigzag t j₂) _ hl₁ hl₂ _ _ _ (or.inr hi)],
    { intros [ident j, ident k],
      apply [expr relation.refl_trans_gen.head] },
    { apply [expr relation.refl_trans_gen.refl] } },
  refine [expr ⟨l.pmap f hf, _, _⟩],
  { refine [expr @@list.chain_pmap_of_chain _ _ _ f (λ x y _ _ h, _) hl₁ h₁₂ _],
    exact [expr zag_of_zag_obj (component.ι _) h] },
  { erw [expr list.last_pmap _ f «expr :: »(j₁, l) (by simpa [] [] [] ["[", expr h₁₂, "]"] [] ["using", expr hf]) (list.cons_ne_nil _ _)] [],
    exact [expr subtype.ext hl₂] }
end

/--
The disjoint union of `J`s connected components, written explicitly as a sigma-type with the
category structure.
This category is equivalent to `J`.
-/
abbrev decomposed (J : Type u₁) [category.{v₁} J] :=
  Σj : connected_components J, component j

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

-- error in CategoryTheory.ConnectedComponents: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance : full (decomposed_to J) :=
{ preimage := begin
    rintro ["⟨", ident j', ",", ident X, ",", ident hX, "⟩", "⟨", ident k', ",", ident Y, ",", ident hY, "⟩", ident f],
    dsimp [] [] [] ["at", ident f],
    have [] [":", expr «expr = »(j', k')] [],
    rw ["[", "<-", expr hX, ",", "<-", expr hY, ",", expr quotient.eq', "]"] [],
    exact [expr relation.refl_trans_gen.single (or.inl ⟨f⟩)],
    subst [expr this],
    refine [expr sigma.sigma_hom.mk f]
  end,
  witness' := begin
    rintro ["⟨", ident j', ",", ident X, ",", ident hX, "⟩", "⟨", "_", ",", ident Y, ",", ident rfl, "⟩", ident f],
    have [] [":", expr «expr = »(quotient.mk' Y, j')] [],
    { rw ["[", "<-", expr hX, ",", expr quotient.eq', "]"] [],
      exact [expr relation.refl_trans_gen.single (or.inr ⟨f⟩)] },
    subst [expr this],
    refl
  end }

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

