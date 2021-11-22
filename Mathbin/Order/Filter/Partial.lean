import Mathbin.Order.Filter.Basic 
import Mathbin.Data.Pfun

/-!
# `tendsto` for relations and partial functions

This file generalizes `filter` definitions from functions to partial functions and relations.

## Considering functions and partial functions as relations

A function `f : α → β` can be considered as the relation `rel α β` which relates `x` and `f x` for
all `x`, and nothing else. This relation is called `function.graph f`.

A partial function `f : α →. β` can be considered as the relation `rel α β` which relates `x` and
`f x` for all `x` for which `f x` exists, and nothing else. This relation is called
`pfun.graph' f`.

In this regard, a function is a relation for which every element in `α` is related to exactly one
element in `β` and a partial function is a relation for which every element in `α` is related to at
most one element in `β`.

This file leverages this analogy to generalize `filter` definitions from functions to partial
functions and relations.

## Notes

`set.preimage` can be generalized to relations in two ways:
* `rel.preimage` returns the image of the set under the inverse relation.
* `rel.core` returns the set of elements that are only related to those in the set.
Both generalizations are sensible in the context of filters, so `filter.comap` and `filter.tendsto`
get two generalizations each.

We first take care of relations. Then the definitions for partial functions are taken as special
cases of the definitions for relations.
-/


universe u v w

namespace Filter

variable{α : Type u}{β : Type v}{γ : Type w}

open_locale Filter

/-! ### Relations -/


/-- The forward map of a filter under a relation. Generalization of `filter.map` to relations. Note
that `rel.core` generalizes `set.preimage`. -/
def rmap (r : Rel α β) (l : Filter α) : Filter β :=
  { Sets := { s | r.core s ∈ l },
    univ_sets :=
      by 
        simp ,
    sets_of_superset := fun s t hs st => mem_of_superset hs$ Rel.core_mono _ st,
    inter_sets :=
      fun s t hs ht =>
        by 
          simp [Rel.core_inter, inter_mem hs ht] }

theorem rmap_sets (r : Rel α β) (l : Filter α) : (l.rmap r).Sets = r.core ⁻¹' l.sets :=
  rfl

@[simp]
theorem mem_rmap (r : Rel α β) (l : Filter α) (s : Set β) : s ∈ l.rmap r ↔ r.core s ∈ l :=
  Iff.rfl

@[simp]
theorem rmap_rmap (r : Rel α β) (s : Rel β γ) (l : Filter α) : rmap s (rmap r l) = rmap (r.comp s) l :=
  filter_eq$
    by 
      simp [rmap_sets, Set.Preimage, Rel.core_comp]

@[simp]
theorem rmap_compose (r : Rel α β) (s : Rel β γ) : (rmap s ∘ rmap r) = rmap (r.comp s) :=
  funext$ rmap_rmap _ _

/-- Generic "limit of a relation" predicate. `rtendsto r l₁ l₂` asserts that for every
`l₂`-neighborhood `a`, the `r`-core of `a` is an `l₁`-neighborhood. One generalization of
`filter.tendsto` to relations. -/
def rtendsto (r : Rel α β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁.rmap r ≤ l₂

theorem rtendsto_def (r : Rel α β) (l₁ : Filter α) (l₂ : Filter β) : rtendsto r l₁ l₂ ↔ ∀ s _ : s ∈ l₂, r.core s ∈ l₁ :=
  Iff.rfl

/-- One way of taking the inverse map of a filter under a relation. One generalization of
`filter.comap` to relations. Note that `rel.core` generalizes `set.preimage`. -/
def rcomap (r : Rel α β) (f : Filter β) : Filter α :=
  { Sets := Rel.Image (fun s t => r.core s ⊆ t) f.sets, univ_sets := ⟨Set.Univ, univ_mem, Set.subset_univ _⟩,
    sets_of_superset := fun a b ⟨a', ha', ma'a⟩ ab => ⟨a', ha', ma'a.trans ab⟩,
    inter_sets :=
      fun a b ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩ =>
        ⟨a' ∩ b', inter_mem ha₁ hb₁, (r.core_inter a' b').Subset.trans (Set.inter_subset_inter ha₂ hb₂)⟩ }

theorem rcomap_sets (r : Rel α β) (f : Filter β) : (rcomap r f).Sets = Rel.Image (fun s t => r.core s ⊆ t) f.sets :=
  rfl

theorem rcomap_rcomap (r : Rel α β) (s : Rel β γ) (l : Filter γ) : rcomap r (rcomap s l) = rcomap (r.comp s) l :=
  filter_eq$
    by 
      ext t 
      simp [rcomap_sets, Rel.Image, Rel.core_comp]
      split 
      ·
        rintro ⟨u, ⟨v, vsets, hv⟩, h⟩
        exact ⟨v, vsets, Set.Subset.trans (Rel.core_mono _ hv) h⟩
      rintro ⟨t, tsets, ht⟩
      exact ⟨Rel.Core s t, ⟨t, tsets, Set.Subset.rfl⟩, ht⟩

@[simp]
theorem rcomap_compose (r : Rel α β) (s : Rel β γ) : (rcomap r ∘ rcomap s) = rcomap (r.comp s) :=
  funext$ rcomap_rcomap _ _

theorem rtendsto_iff_le_rcomap (r : Rel α β) (l₁ : Filter α) (l₂ : Filter β) : rtendsto r l₁ l₂ ↔ l₁ ≤ l₂.rcomap r :=
  by 
    rw [rtendsto_def]
    change (∀ s : Set β, s ∈ l₂.sets → r.core s ∈ l₁) ↔ l₁ ≤ rcomap r l₂ 
    simp [Filter.le_def, rcomap, Rel.mem_image]
    split 
    ·
      exact fun h s t tl₂ => mem_of_superset (h t tl₂)
    ·
      exact fun h t tl₂ => h _ t tl₂ Set.Subset.rfl

/-- One way of taking the inverse map of a filter under a relation. Generalization of `filter.comap`
to relations. -/
def rcomap' (r : Rel α β) (f : Filter β) : Filter α :=
  { Sets := Rel.Image (fun s t => r.preimage s ⊆ t) f.sets, univ_sets := ⟨Set.Univ, univ_mem, Set.subset_univ _⟩,
    sets_of_superset := fun a b ⟨a', ha', ma'a⟩ ab => ⟨a', ha', ma'a.trans ab⟩,
    inter_sets :=
      fun a b ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩ =>
        ⟨a' ∩ b', inter_mem ha₁ hb₁, (@Rel.preimage_inter _ _ r _ _).trans (Set.inter_subset_inter ha₂ hb₂)⟩ }

@[simp]
theorem mem_rcomap' (r : Rel α β) (l : Filter β) (s : Set α) :
  s ∈ l.rcomap' r ↔ ∃ (t : _)(_ : t ∈ l), r.preimage t ⊆ s :=
  Iff.rfl

theorem rcomap'_sets (r : Rel α β) (f : Filter β) :
  (rcomap' r f).Sets = Rel.Image (fun s t => r.preimage s ⊆ t) f.sets :=
  rfl

@[simp]
theorem rcomap'_rcomap' (r : Rel α β) (s : Rel β γ) (l : Filter γ) : rcomap' r (rcomap' s l) = rcomap' (r.comp s) l :=
  Filter.ext$
    fun t =>
      by 
        simp [rcomap'_sets, Rel.Image, Rel.preimage_comp]
        split 
        ·
          rintro ⟨u, ⟨v, vsets, hv⟩, h⟩
          exact ⟨v, vsets, (Rel.preimage_mono _ hv).trans h⟩
        rintro ⟨t, tsets, ht⟩
        exact ⟨s.preimage t, ⟨t, tsets, Set.Subset.rfl⟩, ht⟩

@[simp]
theorem rcomap'_compose (r : Rel α β) (s : Rel β γ) : (rcomap' r ∘ rcomap' s) = rcomap' (r.comp s) :=
  funext$ rcomap'_rcomap' _ _

/-- Generic "limit of a relation" predicate. `rtendsto' r l₁ l₂` asserts that for every
`l₂`-neighborhood `a`, the `r`-preimage of `a` is an `l₁`-neighborhood. One generalization of
`filter.tendsto` to relations. -/
def rtendsto' (r : Rel α β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁ ≤ l₂.rcomap' r

theorem rtendsto'_def (r : Rel α β) (l₁ : Filter α) (l₂ : Filter β) :
  rtendsto' r l₁ l₂ ↔ ∀ s _ : s ∈ l₂, r.preimage s ∈ l₁ :=
  by 
    unfold rtendsto' rcomap' 
    simp [le_def, Rel.mem_image]
    split 
    ·
      exact fun h s hs => h _ _ hs Set.Subset.rfl
    ·
      exact fun h s t ht => mem_of_superset (h t ht)

theorem tendsto_iff_rtendsto (l₁ : Filter α) (l₂ : Filter β) (f : α → β) :
  tendsto f l₁ l₂ ↔ rtendsto (Function.Graph f) l₁ l₂ :=
  by 
    simp [tendsto_def, Function.Graph, rtendsto_def, Rel.Core, Set.Preimage]

theorem tendsto_iff_rtendsto' (l₁ : Filter α) (l₂ : Filter β) (f : α → β) :
  tendsto f l₁ l₂ ↔ rtendsto' (Function.Graph f) l₁ l₂ :=
  by 
    simp [tendsto_def, Function.Graph, rtendsto'_def, Rel.preimage_def, Set.Preimage]

/-! ### Partial functions -/


/-- The forward map of a filter under a partial function. Generalization of `filter.map` to partial
functions. -/
def pmap (f : α →. β) (l : Filter α) : Filter β :=
  Filter.rmap f.graph' l

@[simp]
theorem mem_pmap (f : α →. β) (l : Filter α) (s : Set β) : s ∈ l.pmap f ↔ f.core s ∈ l :=
  Iff.rfl

/-- Generic "limit of a partial function" predicate. `ptendsto r l₁ l₂` asserts that for every
`l₂`-neighborhood `a`, the `p`-core of `a` is an `l₁`-neighborhood. One generalization of
`filter.tendsto` to partial function. -/
def ptendsto (f : α →. β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁.pmap f ≤ l₂

theorem ptendsto_def (f : α →. β) (l₁ : Filter α) (l₂ : Filter β) : ptendsto f l₁ l₂ ↔ ∀ s _ : s ∈ l₂, f.core s ∈ l₁ :=
  Iff.rfl

theorem ptendsto_iff_rtendsto (l₁ : Filter α) (l₂ : Filter β) (f : α →. β) :
  ptendsto f l₁ l₂ ↔ rtendsto f.graph' l₁ l₂ :=
  Iff.rfl

theorem pmap_res (l : Filter α) (s : Set α) (f : α → β) : pmap (Pfun.res f s) l = map f (l⊓𝓟 s) :=
  by 
    ext t 
    simp only [Pfun.core_res, mem_pmap, mem_map, mem_inf_principal, imp_iff_not_or]
    rfl

theorem tendsto_iff_ptendsto (l₁ : Filter α) (l₂ : Filter β) (s : Set α) (f : α → β) :
  tendsto f (l₁⊓𝓟 s) l₂ ↔ ptendsto (Pfun.res f s) l₁ l₂ :=
  by 
    simp only [tendsto, ptendsto, pmap_res]

theorem tendsto_iff_ptendsto_univ (l₁ : Filter α) (l₂ : Filter β) (f : α → β) :
  tendsto f l₁ l₂ ↔ ptendsto (Pfun.res f Set.Univ) l₁ l₂ :=
  by 
    rw [←tendsto_iff_ptendsto]
    simp [principal_univ]

/-- Inverse map of a filter under a partial function. One generalization of `filter.comap` to
partial functions. -/
def pcomap' (f : α →. β) (l : Filter β) : Filter α :=
  Filter.rcomap' f.graph' l

/-- Generic "limit of a partial function" predicate. `ptendsto' r l₁ l₂` asserts that for every
`l₂`-neighborhood `a`, the `p`-preimage of `a` is an `l₁`-neighborhood. One generalization of
`filter.tendsto` to partial functions. -/
def ptendsto' (f : α →. β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁ ≤ l₂.rcomap' f.graph'

theorem ptendsto'_def (f : α →. β) (l₁ : Filter α) (l₂ : Filter β) :
  ptendsto' f l₁ l₂ ↔ ∀ s _ : s ∈ l₂, f.preimage s ∈ l₁ :=
  rtendsto'_def _ _ _

theorem ptendsto_of_ptendsto' {f : α →. β} {l₁ : Filter α} {l₂ : Filter β} : ptendsto' f l₁ l₂ → ptendsto f l₁ l₂ :=
  by 
    rw [ptendsto_def, ptendsto'_def]
    exact fun h s sl₂ => mem_of_superset (h s sl₂) (Pfun.preimage_subset_core _ _)

theorem ptendsto'_of_ptendsto {f : α →. β} {l₁ : Filter α} {l₂ : Filter β} (h : f.dom ∈ l₁) :
  ptendsto f l₁ l₂ → ptendsto' f l₁ l₂ :=
  by 
    rw [ptendsto_def, ptendsto'_def]
    intro h' s sl₂ 
    rw [Pfun.preimage_eq]
    exact inter_mem (h' s sl₂) h

end Filter

