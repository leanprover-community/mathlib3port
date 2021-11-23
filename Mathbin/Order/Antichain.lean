import Mathbin.Data.Set.Pairwise

/-!
# Antichains

This file defines antichains. An antichain is a set where any two distinct elements are not related.
If the relation is `(≤)`, this corresponds to incomparability and usual order antichains. If the
relation is `G.adj` for `G : simple_graph α`, this corresponds to independent sets of `G`.

## Definitions

* `is_antichain r s`: Any two elements of `s : set α` are unrelated by `r : α → α → Prop`.
* `is_antichain.mk r s`: Turns `s` into an antichain by keeping only the "maximal" elements.
-/


open Function Set

variable{α β : Type _}{r r₁ r₂ : α → α → Prop}{r' : β → β → Prop}{s t : Set α}{a : α}

protected theorem Symmetric.compl (h : Symmetric r) : Symmetric («expr ᶜ» r) :=
  fun x y hr hr' => hr$ h hr'

/-- An antichain is a set such that no two distinct elements are related. -/
def IsAntichain (r : α → α → Prop) (s : Set α) : Prop :=
  s.pairwise («expr ᶜ» r)

namespace IsAntichain

protected theorem subset (hs : IsAntichain r s) (h : t ⊆ s) : IsAntichain r t :=
  hs.mono h

theorem mono (hs : IsAntichain r₁ s) (h : r₂ ≤ r₁) : IsAntichain r₂ s :=
  hs.mono'$ compl_le_compl h

theorem mono_on (hs : IsAntichain r₁ s) (h : s.pairwise fun ⦃a b⦄ => r₂ a b → r₁ a b) : IsAntichain r₂ s :=
  hs.imp_on$ h.imp$ fun a b h h₁ h₂ => h₁$ h h₂

theorem eq_of_related (hs : IsAntichain r s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) (h : r a b) : a = b :=
  of_not_not$ fun hab => hs _ ha _ hb hab h

protected theorem IsAntisymm (h : IsAntichain r univ) : IsAntisymm α r :=
  ⟨fun a b ha _ => h.eq_of_related trivialₓ trivialₓ ha⟩

protected theorem Subsingleton [IsTrichotomous α r] (h : IsAntichain r s) : s.subsingleton :=
  by 
    rintro a ha b hb 
    obtain hab | hab | hab := trichotomous_of r a b
    ·
      exact h.eq_of_related ha hb hab
    ·
      exact hab
    ·
      exact (h.eq_of_related hb ha hab).symm

protected theorem flip (hs : IsAntichain r s) : IsAntichain (flip r) s :=
  fun a ha b hb h => hs _ hb _ ha h.symm

theorem swap (hs : IsAntichain r s) : IsAntichain (swap r) s :=
  hs.flip

theorem image (hs : IsAntichain r s) (f : α → β) (h : ∀ ⦃a b⦄, r' (f a) (f b) → r a b) : IsAntichain r' (f '' s) :=
  by 
    rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ hbc hr 
    exact hs _ hb _ hc (ne_of_apply_ne _ hbc) (h hr)

theorem preimage (hs : IsAntichain r s) {f : β → α} (hf : injective f) (h : ∀ ⦃a b⦄, r' a b → r (f a) (f b)) :
  IsAntichain r' (f ⁻¹' s) :=
  fun b hb c hc hbc hr => hs _ hb _ hc (hf.ne hbc)$ h hr

theorem _root_.is_antichain_insert :
  IsAntichain r (insert a s) ↔ IsAntichain r s ∧ ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬r a b ∧ ¬r b a :=
  Set.pairwise_insert

protected theorem insert (hs : IsAntichain r s) (hl : ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬r b a)
  (hr : ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬r a b) : IsAntichain r (insert a s) :=
  is_antichain_insert.2 ⟨hs, fun b hb hab => ⟨hr hb hab, hl hb hab⟩⟩

theorem _root_.is_antichain_insert_of_symmetric (hr : Symmetric r) :
  IsAntichain r (insert a s) ↔ IsAntichain r s ∧ ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬r a b :=
  pairwise_insert_of_symmetric hr.compl

theorem insert_of_symmetric (hs : IsAntichain r s) (hr : Symmetric r) (h : ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬r a b) :
  IsAntichain r (insert a s) :=
  (is_antichain_insert_of_symmetric hr).2 ⟨hs, h⟩

/-- Turns a set into an antichain by keeping only the "maximal" elements. -/
protected def mk (r : α → α → Prop) (s : Set α) : Set α :=
  { a∈s | ∀ ⦃b⦄, b ∈ s → r a b → a = b }

theorem mk_is_antichain (r : α → α → Prop) (s : Set α) : IsAntichain r (IsAntichain.Mk r s) :=
  fun a ha b hb hab h => hab$ ha.2 hb.1 h

theorem mk_subset : IsAntichain.Mk r s ⊆ s :=
  sep_subset _ _

/-- If `is_antichain.mk r s` is included in but *shadows* the antichain `t`, then it is actually
equal to `t`. -/
theorem mk_max (ht : IsAntichain r t) (h : IsAntichain.Mk r s ⊆ t)
  (hs : ∀ ⦃a⦄, a ∈ t → ∃ (b : _)(_ : b ∈ IsAntichain.Mk r s), r a b) : t = IsAntichain.Mk r s :=
  by 
    refine' subset.antisymm (fun a ha => _) h 
    obtain ⟨b, hb, hr⟩ := hs ha 
    rwa [of_not_not fun hab => ht _ ha _ (h hb) hab hr]

end IsAntichain

theorem Set.Subsingleton.is_antichain (hs : s.subsingleton) (r : α → α → Prop) : IsAntichain r s :=
  hs.pairwise _

