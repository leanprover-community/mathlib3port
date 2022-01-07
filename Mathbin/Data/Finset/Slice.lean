import Mathbin.Data.Fintype.Basic
import Mathbin.Order.Antichain

/-!
# `r`-sets and slice

This file defines the `r`-th slice of a set family and provides a way to say that a set family is
made of `r`-sets.

An `r`-set is a finset of cardinality `r` (aka of *size* `r`). The `r`-th slice of a set family is
the set family made of its `r`-sets.

## Main declarations

* `set.sized`: `A.sized r` means that `A` only contains `r`-sets.
* `finset.slice`: `A.slice r` is the set of `r`-sets in `A`.

## Notation

`A # r` is notation for `A.slice r` in locale `finset_family`.
-/


open Finset Nat

variable {α : Type _}

namespace Set

variable {A B : Set (Finset α)} {r : ℕ}

/-! ### Families of `r`-sets -/


/-- `sized r A` means that every finset in `A` has size `r`. -/
def sized (r : ℕ) (A : Set (Finset α)) : Prop :=
  ∀ ⦃x⦄, x ∈ A → card x = r

theorem sized.mono (h : A ⊆ B) (hB : B.sized r) : A.sized r := fun x hx => hB $ h hx

theorem sized_union : (A ∪ B).Sized r ↔ A.sized r ∧ B.sized r :=
  ⟨fun hA => ⟨hA.mono $ subset_union_left _ _, hA.mono $ subset_union_right _ _⟩, fun hA x hx =>
    (hx.elim fun h => hA.1 h) $ fun h => hA.2 h⟩

alias sized_union ↔ _ Set.Sized.union

protected theorem sized.is_antichain (hA : A.sized r) : IsAntichain (· ⊆ ·) A := fun s hs t ht h hst =>
  h $ eq_of_subset_of_card_le hst ((hA ht).trans (hA hs).symm).le

end Set

namespace Finset

section Sized

variable [Fintype α] {𝒜 : Finset (Finset α)} {s : Finset α} {r : ℕ}

theorem subset_powerset_len_univ_iff : 𝒜 ⊆ powerset_len r univ ↔ (𝒜 : Set (Finset α)).Sized r :=
  forall_congrₓ $ fun A => by
    rw [mem_powerset_len_univ_iff, mem_coe]

alias subset_powerset_len_univ_iff ↔ _ Set.Sized.subset_powerset_len_univ

theorem _root_.set.sized.card_le (h𝒜 : (𝒜 : Set (Finset α)).Sized r) : card 𝒜 ≤ (Fintype.card α).choose r := by
  rw [Fintype.card, ← card_powerset_len]
  exact card_le_of_subset h𝒜.subset_powerset_len_univ

end Sized

/-! ### Slices -/


section Slice

variable {𝒜 : Finset (Finset α)} {A A₁ A₂ : Finset α} {r r₁ r₂ : ℕ}

/-- The `r`-th slice of a set family is the subset of its elements which have cardinality `r`. -/
def slice (𝒜 : Finset (Finset α)) (r : ℕ) : Finset (Finset α) :=
  𝒜.filter fun i => i.card = r

localized [FinsetFamily] infixl:90 " # " => Finset.slice

/-- `A` is in the `r`-th slice of `𝒜` iff it's in `𝒜` and has cardinality `r`. -/
theorem mem_slice : A ∈ 𝒜 # r ↔ A ∈ 𝒜 ∧ A.card = r :=
  mem_filter

/-- The `r`-th slice of `𝒜` is a subset of `𝒜`. -/
theorem slice_subset : 𝒜 # r ⊆ 𝒜 :=
  filter_subset _ _

/-- Everything in the `r`-th slice of `𝒜` has size `r`. -/
theorem sized_slice : (𝒜 # r : Set (Finset α)).Sized r := fun _ => And.right ∘ mem_slice.mp

theorem eq_of_mem_slice (h₁ : A ∈ 𝒜 # r₁) (h₂ : A ∈ 𝒜 # r₂) : r₁ = r₂ :=
  (sized_slice h₁).symm.trans $ sized_slice h₂

/-- Elements in distinct slices must be distinct. -/
theorem ne_of_mem_slice (h₁ : A₁ ∈ 𝒜 # r₁) (h₂ : A₂ ∈ 𝒜 # r₂) : r₁ ≠ r₂ → A₁ ≠ A₂ :=
  mt $ fun h => (sized_slice h₁).symm.trans ((congr_argₓ card h).trans (sized_slice h₂))

variable [DecidableEq α]

theorem pairwise_disjoint_slice : (Set.Univ : Set ℕ).PairwiseDisjoint (slice 𝒜) := fun m _ n _ hmn =>
  disjoint_filter.2 $ fun s hs hm hn => hmn $ hm.symm.trans hn

end Slice

end Finset

