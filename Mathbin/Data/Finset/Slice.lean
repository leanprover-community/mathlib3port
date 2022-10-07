/-
Copyright (c) 2021 Bhavik Mehta, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, Yaël Dillies
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.Nat.Interval
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


open Finsetₓ Nat

open BigOperators

variable {α : Type _} {ι : Sort _} {κ : ι → Sort _}

namespace Set

variable {A B : Set (Finsetₓ α)} {r : ℕ}

/-! ### Families of `r`-sets -/


/-- `sized r A` means that every finset in `A` has size `r`. -/
def Sized (r : ℕ) (A : Set (Finsetₓ α)) : Prop :=
  ∀ ⦃x⦄, x ∈ A → card x = r

theorem Sized.mono (h : A ⊆ B) (hB : B.Sized r) : A.Sized r := fun x hx => hB <| h hx

theorem sized_union : (A ∪ B).Sized r ↔ A.Sized r ∧ B.Sized r :=
  ⟨fun hA => ⟨hA.mono <| subset_union_left _ _, hA.mono <| subset_union_right _ _⟩, fun hA x hx =>
    (hx.elim fun h => hA.1 h) fun h => hA.2 h⟩

alias sized_union ↔ _ sized.union

--TODO: A `forall_Union` lemma would be handy here.
@[simp]
theorem sized_Union {f : ι → Set (Finsetₓ α)} : (⋃ i, f i).Sized r ↔ ∀ i, (f i).Sized r := by
  simp_rw [Set.Sized, Set.mem_Union, forall_exists_index]
  exact forall_swap

-- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j)
@[simp]
theorem sized_Union₂ {f : ∀ i, κ i → Set (Finsetₓ α)} : (⋃ (i) (j), f i j).Sized r ↔ ∀ i j, (f i j).Sized r := by
  simp_rw [sized_Union]

protected theorem Sized.is_antichain (hA : A.Sized r) : IsAntichain (· ⊆ ·) A := fun s hs t ht h hst =>
  h <| Finsetₓ.eq_of_subset_of_card_le hst ((hA ht).trans (hA hs).symm).le

protected theorem Sized.subsingleton (hA : A.Sized 0) : A.Subsingleton :=
  (subsingleton_of_forall_eq ∅) fun s hs => card_eq_zero.1 <| hA hs

theorem Sized.subsingleton' [Fintypeₓ α] (hA : A.Sized (Fintypeₓ.card α)) : A.Subsingleton :=
  (subsingleton_of_forall_eq Finsetₓ.univ) fun s hs => s.card_eq_iff_eq_univ.1 <| hA hs

theorem Sized.empty_mem_iff (hA : A.Sized r) : ∅ ∈ A ↔ A = {∅} :=
  hA.IsAntichain.bot_mem_iff

theorem Sized.univ_mem_iff [Fintypeₓ α] (hA : A.Sized r) : Finsetₓ.univ ∈ A ↔ A = {Finsetₓ.univ} :=
  hA.IsAntichain.top_mem_iff

theorem sized_powerset_len (s : Finsetₓ α) (r : ℕ) : (powersetLen r s : Set (Finsetₓ α)).Sized r := fun t ht =>
  (mem_powerset_len.1 ht).2

end Set

namespace Finsetₓ

section Sized

variable [Fintypeₓ α] {𝒜 : Finsetₓ (Finsetₓ α)} {s : Finsetₓ α} {r : ℕ}

theorem subset_powerset_len_univ_iff : 𝒜 ⊆ powersetLen r univ ↔ (𝒜 : Set (Finsetₓ α)).Sized r :=
  forall_congrₓ fun A => by rw [mem_powerset_len_univ_iff, mem_coe]

alias subset_powerset_len_univ_iff ↔ _ _root_.set.sized.subset_powerset_len_univ

theorem _root_.set.sized.card_le (h𝒜 : (𝒜 : Set (Finsetₓ α)).Sized r) : card 𝒜 ≤ (Fintypeₓ.card α).choose r := by
  rw [Fintypeₓ.card, ← card_powerset_len]
  exact card_le_of_subset h𝒜.subset_powerset_len_univ

end Sized

/-! ### Slices -/


section Slice

variable {𝒜 : Finsetₓ (Finsetₓ α)} {A A₁ A₂ : Finsetₓ α} {r r₁ r₂ : ℕ}

/-- The `r`-th slice of a set family is the subset of its elements which have cardinality `r`. -/
def slice (𝒜 : Finsetₓ (Finsetₓ α)) (r : ℕ) : Finsetₓ (Finsetₓ α) :=
  𝒜.filter fun i => i.card = r

-- mathport name: finset.slice
localized [FinsetFamily] infixl:90 " # " => Finsetₓ.slice

/-- `A` is in the `r`-th slice of `𝒜` iff it's in `𝒜` and has cardinality `r`. -/
theorem mem_slice : A ∈ 𝒜 # r ↔ A ∈ 𝒜 ∧ A.card = r :=
  mem_filter

/-- The `r`-th slice of `𝒜` is a subset of `𝒜`. -/
theorem slice_subset : 𝒜 # r ⊆ 𝒜 :=
  filter_subset _ _

/-- Everything in the `r`-th slice of `𝒜` has size `r`. -/
theorem sized_slice : (𝒜 # r : Set (Finsetₓ α)).Sized r := fun _ => And.right ∘ mem_slice.mp

theorem eq_of_mem_slice (h₁ : A ∈ 𝒜 # r₁) (h₂ : A ∈ 𝒜 # r₂) : r₁ = r₂ :=
  (sized_slice h₁).symm.trans <| sized_slice h₂

/-- Elements in distinct slices must be distinct. -/
theorem ne_of_mem_slice (h₁ : A₁ ∈ 𝒜 # r₁) (h₂ : A₂ ∈ 𝒜 # r₂) : r₁ ≠ r₂ → A₁ ≠ A₂ :=
  mt fun h => (sized_slice h₁).symm.trans ((congr_arg card h).trans (sized_slice h₂))

theorem pairwise_disjoint_slice [DecidableEq α] : (Set.Univ : Set ℕ).PairwiseDisjoint (slice 𝒜) := fun m _ n _ hmn =>
  disjoint_filter.2 fun s hs hm hn => hmn <| hm.symm.trans hn

variable [Fintypeₓ α] (𝒜)

@[simp]
theorem bUnion_slice [DecidableEq α] : (Iic <| Fintypeₓ.card α).bUnion 𝒜.slice = 𝒜 :=
  (Subset.antisymm (bUnion_subset.2 fun r _ => slice_subset)) fun s hs =>
    mem_bUnion.2 ⟨s.card, mem_Iic.2 <| s.card_le_univ, mem_slice.2 <| ⟨hs, rfl⟩⟩

@[simp]
theorem sum_card_slice : (∑ r in iic (Fintypeₓ.card α), (𝒜 # r).card) = 𝒜.card := by
  rw [← card_bUnion (finset.pairwise_disjoint_slice.subset (Set.subset_univ _)), bUnion_slice]
  exact Classical.decEq _

end Slice

end Finsetₓ

