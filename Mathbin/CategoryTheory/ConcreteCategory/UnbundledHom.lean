import Mathbin.CategoryTheory.ConcreteCategory.BundledHom

/-!
# Category instances for structures that use unbundled homs

This file provides basic infrastructure to define concrete
categories using unbundled homs (see `class unbundled_hom`), and
define forgetful functors between them (see
`unbundled_hom.mk_has_forget₂`).
-/


universe v u

namespace CategoryTheory

/-- A class for unbundled homs used to define a category. `hom` must
take two types `α`, `β` and instances of the corresponding structures,
and return a predicate on `α → β`. -/
class unbundled_hom{c : Type u → Type u}(hom : ∀ {α β}, c α → c β → (α → β) → Prop) where 
  hom_id{} : ∀ {α} (ia : c α), hom ia ia id 
  hom_comp{} :
  ∀ {α β γ} {Iα : c α} {Iβ : c β} {Iγ : c γ} {g : β → γ} {f : α → β} (hg : hom Iβ Iγ g) (hf : hom Iα Iβ f),
    hom Iα Iγ (g ∘ f)

namespace UnbundledHom

variable(c : Type u → Type u)(hom : ∀ ⦃α β⦄, c α → c β → (α → β) → Prop)[𝒞 : unbundled_hom hom]

include 𝒞

-- error in CategoryTheory.ConcreteCategory.UnbundledHom: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
instance bundled_hom : bundled_hom (λ (α β) (Iα : c α) (Iβ : c β), subtype (hom Iα Iβ)) :=
{ to_fun := λ _ _ _ _, subtype.val,
  id := λ α Iα, ⟨id, hom_id hom Iα⟩,
  id_to_fun := by intros []; refl,
  comp := λ _ _ _ _ _ _ g f, ⟨«expr ∘ »(g.1, f.1), hom_comp c g.2 f.2⟩,
  comp_to_fun := by intros []; refl,
  hom_ext := by intros []; apply [expr subtype.eq] }

section HasForget₂

variable{c hom}{c' : Type u → Type u}{hom' : ∀ ⦃α β⦄, c' α → c' β → (α → β) → Prop}[𝒞' : unbundled_hom hom']

include 𝒞'

variable(obj : ∀ ⦃α⦄, c α → c' α)(map : ∀ ⦃α β Iα Iβ f⦄, @hom α β Iα Iβ f → hom' (obj Iα) (obj Iβ) f)

/-- A custom constructor for forgetful functor
between concrete categories defined using `unbundled_hom`. -/
def mk_has_forget₂ : has_forget₂ (bundled c) (bundled c') :=
  bundled_hom.mk_has_forget₂ obj (fun X Y f => ⟨f.val, map f.property⟩) fun _ _ _ => rfl

end HasForget₂

end UnbundledHom

end CategoryTheory

