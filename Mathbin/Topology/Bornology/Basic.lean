/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathbin.Order.Filter.Cofinite

/-!
# Basic theory of bornology

We develop the basic theory of bornologies. Instead of axiomatizing bounded sets and defining
bornologies in terms of those, we recognize that the cobounded sets form a filter and define a
bornology as a filter of cobounded sets which contains the cofinite filter.  This allows us to make
use of the extensive library for filters, but we also provide the relevant connecting results for
bounded sets.

The specification of a bornology in terms of the cobounded filter is equivalent to the standard
one (e.g., see [Bourbaki, *Topological Vector Spaces*][bourbaki1987], **covering bornology**, now
often called simply **bornology**) in terms of bounded sets (see `bornology.of_bounded`,
`is_bounded.union`, `is_bounded.subset`), except that we do not allow the empty bornology (that is,
we require that *some* set must be bounded; equivalently, `∅` is bounded). In the literature the
cobounded filter is generally referred to as the *filter at infinity*.

## Main definitions

- `bornology α`: a class consisting of `cobounded : filter α` and a proof that this filter
  contains the `cofinite` filter.
- `bornology.is_cobounded`: the predicate that a set is a member of the `cobounded α` filter. For
  `s : set α`, one should prefer `bornology.is_cobounded s` over `s ∈ cobounded α`.
- `bornology.is_bounded`: the predicate that states a set is bounded (i.e., the complement of a
  cobounded set). One should prefer `bornology.is_bounded s` over `sᶜ ∈ cobounded α`.
- `bounded_space α`: a class extending `bornology α` with the condition
  `bornology.is_bounded (set.univ : set α)`

Although use of `cobounded α` is discouraged for indicating the (co)boundedness of individual sets,
it is intended for regular use as a filter on `α`.
-/


open Set Filter

variable {α β : Type _}

/-- A **bornology** on a type `α` is a filter of cobounded sets which contains the cofinite filter.
Such spaces are equivalently specified by their bounded sets, see `bornology.of_bounded`
and `bornology.ext_iff_is_bounded`-/
@[ext]
class Bornology (α : Type _) where
  cobounded {} : Filter α
  le_cofinite {} : cobounded ≤ cofinite

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (s₁ s₂ «expr ∈ » B)
/-- A constructor for bornologies by specifying the bounded sets,
and showing that they satisfy the appropriate conditions. -/
@[simps]
def Bornology.ofBounded {α : Type _} (B : Set (Set α)) (empty_mem : ∅ ∈ B)
    (subset_mem : ∀, ∀ s₁ ∈ B, ∀, ∀ s₂ : Set α, s₂ ⊆ s₁ → s₂ ∈ B)
    (union_mem : ∀ s₁ s₂ _ : s₁ ∈ B _ : s₂ ∈ B, s₁ ∪ s₂ ∈ B) (sUnion_univ : ⋃₀B = univ) : Bornology α where
  cobounded :=
    { Sets := { s : Set α | sᶜ ∈ B },
      univ_sets := by
        rwa [← compl_univ] at empty_mem,
      sets_of_superset := fun x y hx hy => subset_mem (xᶜ) hx (yᶜ) (compl_subset_compl.mpr hy),
      inter_sets := fun x y hx hy => by
        simpa [compl_inter] using union_mem (xᶜ) hx (yᶜ) hy }
  le_cofinite := by
    refine' le_def.mpr fun s => _
    simp only [mem_set_of_eq, mem_cofinite, Filter.mem_mk]
    generalize sᶜ = s'
    refine' fun h => h.dinduction_on _ fun x t hx ht h => _
    · exact empty_mem
      
    · refine' insert_eq x t ▸ union_mem _ _ _ h
      obtain ⟨b, hb : b ∈ B, hxb : x ∈ b⟩ :=
        mem_sUnion.mp
          (by
            simpa [← sUnion_univ] using mem_univ x)
      exact subset_mem _ hb _ (singleton_subset_iff.mpr hxb)
      

namespace Bornology

section

variable [Bornology α] {s₁ s₂ : Set α}

/-- `is_cobounded` is the predicate that `s` is in the filter of cobounded sets in the ambient
bornology on `α` -/
def IsCobounded (s : Set α) : Prop :=
  s ∈ cobounded α

/-- `is_bounded` is the predicate that `s` is bounded relative to the ambient bornology on `α`. -/
def IsBounded (s : Set α) : Prop :=
  sᶜ ∈ cobounded α

theorem is_cobounded_def {s : Set α} : IsCobounded s ↔ s ∈ cobounded α :=
  Iff.rfl

theorem is_bounded_def {s : Set α} : IsBounded s ↔ sᶜ ∈ cobounded α :=
  Iff.rfl

theorem is_bounded_compl_iff {s : Set α} : IsBounded (sᶜ) ↔ IsCobounded s := by
  rw [is_bounded_def, is_cobounded_def, compl_compl]

@[simp]
theorem is_bounded_empty : IsBounded (∅ : Set α) := by
  rw [is_bounded_def, compl_empty]
  exact univ_mem

theorem IsBounded.union (h₁ : IsBounded s₁) (h₂ : IsBounded s₂) : IsBounded (s₁ ∪ s₂) := by
  rw [is_bounded_def, compl_union]
  exact (cobounded α).inter_sets h₁ h₂

theorem IsBounded.subset (h₁ : IsBounded s₂) (h₂ : s₁ ⊆ s₂) : IsBounded s₁ := by
  rw [is_bounded_def]
  exact (cobounded α).sets_of_superset h₁ (compl_subset_compl.mpr h₂)

@[simp]
theorem sUnion_bounded_univ : ⋃₀{ s : Set α | IsBounded s } = Set.Univ :=
  univ_subset_iff.mp fun x hx =>
    mem_sUnion_of_mem (mem_singleton x) <|
      le_def.mp (le_cofinite α) ({x}ᶜ) <| (Set.finite_singleton x).compl_mem_cofinite

end

theorem ext_iff' {t t' : Bornology α} : t = t' ↔ ∀ s, (@cobounded α t).Sets s ↔ (@cobounded α t').Sets s :=
  ⟨fun h s => h ▸ Iff.rfl, fun h => by
    ext
    exact h _⟩

theorem ext_iff_is_bounded {t t' : Bornology α} : t = t' ↔ ∀ s, @IsBounded α t s ↔ @IsBounded α t' s :=
  ⟨fun h s => h ▸ Iff.rfl, fun h => by
    ext
    simpa only [is_bounded_def, compl_compl] using h (sᶜ)⟩

variable [Bornology α]

theorem is_bounded_sUnion {s : Set (Set α)} (hs : Finite s) : (∀, ∀ t ∈ s, ∀, IsBounded t) → IsBounded (⋃₀s) :=
  (Finite.induction_on hs fun _ => by
      rw [sUnion_empty]
      exact is_bounded_empty)
    fun a s has hs ih h => by
    rw [sUnion_insert]
    exact is_bounded.union (h _ <| mem_insert _ _) (ih fun t => h t ∘ mem_insert_of_mem _)

theorem is_bounded_bUnion {s : Set β} {f : β → Set α} (hs : Finite s) :
    (∀, ∀ i ∈ s, ∀, IsBounded (f i)) → IsBounded (⋃ i ∈ s, f i) :=
  Finite.induction_on hs
    (fun _ => by
      rw [bUnion_empty]
      exact is_bounded_empty)
    fun a s has hs ih h => by
    rw [bUnion_insert]
    exact is_bounded.union (h a (mem_insert _ _)) (ih fun i hi => h i (mem_insert_of_mem _ hi))

theorem is_bounded_Union [Fintype β] {s : β → Set α} (h : ∀ i, IsBounded (s i)) : IsBounded (⋃ i, s i) := by
  simpa using is_bounded_bUnion finite_univ fun i _ => h i

end Bornology

instance : Bornology PUnit :=
  ⟨⊥, bot_le⟩

/-- The cofinite filter as a bornology -/
@[reducible]
def Bornology.cofinite : Bornology α where
  cobounded := cofinite
  le_cofinite := le_reflₓ _

/-- A **bounded space** is a `bornology α` such that `set.univ : set α` is bounded. -/
class BoundedSpace extends Bornology α where
  bounded_univ : Bornology.IsBounded (Univ : Set α)

