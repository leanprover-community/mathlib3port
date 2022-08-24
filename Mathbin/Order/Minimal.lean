/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.Antichain
import Mathbin.Order.UpperLower

/-!
# Minimal/maximal elements of a set

This file defines minimal and maximal of a set with respect to an arbitrary relation.

## Main declarations

* `maximals r s`: Maximal elements of `s` with respect to `r`.
* `minimals r s`: Minimal elements of `s` with respect to `r`.

## TODO

Do we need a `finset` version?
-/


open Function Set

variable {α : Type _} (r r₁ r₂ : α → α → Prop) (s t : Set α) (a b : α)

/-- Turns a set into an antichain by keeping only the "maximal" elements. -/
def Maximals : Set α :=
  { a ∈ s | ∀ ⦃b⦄, b ∈ s → r a b → r b a }

/-- Turns a set into an antichain by keeping only the "minimal" elements. -/
def Minimals : Set α :=
  { a ∈ s | ∀ ⦃b⦄, b ∈ s → r b a → r a b }

theorem maximals_subset : Maximals r s ⊆ s :=
  sep_subset _ _

theorem minimals_subset : Minimals r s ⊆ s :=
  sep_subset _ _

@[simp]
theorem maximals_empty : Maximals r ∅ = ∅ :=
  sep_empty _

@[simp]
theorem minimals_empty : Minimals r ∅ = ∅ :=
  sep_empty _

@[simp]
theorem maximals_singleton : Maximals r {a} = {a} :=
  (maximals_subset _ _).antisymm <|
    singleton_subset_iff.2 <|
      ⟨rfl, by
        rintro b (rfl : b = a)
        exact id⟩

@[simp]
theorem minimals_singleton : Minimals r {a} = {a} :=
  maximals_singleton _ _

theorem maximals_swap : Maximals (swap r) s = Minimals r s :=
  rfl

theorem minimals_swap : Minimals (swap r) s = Maximals r s :=
  rfl

section IsAntisymm

variable {r s t a b} [IsAntisymm α r]

theorem eq_of_mem_maximals (ha : a ∈ Maximals r s) (hb : b ∈ s) (h : r a b) : a = b :=
  antisymm h <| ha.2 hb h

theorem eq_of_mem_minimals (ha : a ∈ Minimals r s) (hb : b ∈ s) (h : r b a) : a = b :=
  antisymm (ha.2 hb h) h

variable (r s)

theorem maximals_antichain : IsAntichain r (Maximals r s) := fun a ha b hb hab h => hab <| eq_of_mem_maximals ha hb.1 h

theorem minimals_antichain : IsAntichain r (Minimals r s) := by
  haveI := IsAntisymm.swap r
  exact (maximals_antichain _ _).swap

end IsAntisymm

theorem maximals_eq_minimals [IsSymm α r] : Maximals r s = Minimals r s := by
  congr
  ext a b
  exact comm

variable {r r₁ r₂ s t a}

theorem Set.Subsingleton.maximals_eq (h : s.Subsingleton) : Maximals r s = s :=
  h.induction_on (minimals_empty _) (maximals_singleton _)

theorem Set.Subsingleton.minimals_eq (h : s.Subsingleton) : Minimals r s = s :=
  h.maximals_eq

theorem maximals_mono [IsAntisymm α r₂] (h : ∀ a b, r₁ a b → r₂ a b) : Maximals r₂ s ⊆ Maximals r₁ s := fun a ha =>
  ⟨ha.1, fun b hb hab => by
    have := eq_of_mem_maximals ha hb (h _ _ hab)
    subst this
    exact hab⟩

theorem minimals_mono [IsAntisymm α r₂] (h : ∀ a b, r₁ a b → r₂ a b) : Minimals r₂ s ⊆ Minimals r₁ s := fun a ha =>
  ⟨ha.1, fun b hb hab => by
    have := eq_of_mem_minimals ha hb (h _ _ hab)
    subst this
    exact hab⟩

theorem maximals_union : Maximals r (s ∪ t) ⊆ Maximals r s ∪ Maximals r t := by
  intro a ha
  obtain h | h := ha.1
  · exact Or.inl ⟨h, fun b hb => ha.2 <| Or.inl hb⟩
    
  · exact Or.inr ⟨h, fun b hb => ha.2 <| Or.inr hb⟩
    

theorem minimals_union : Minimals r (s ∪ t) ⊆ Minimals r s ∪ Minimals r t :=
  maximals_union

theorem maximals_inter_subset : Maximals r s ∩ t ⊆ Maximals r (s ∩ t) := fun a ha =>
  ⟨⟨ha.1.1, ha.2⟩, fun b hb => ha.1.2 hb.1⟩

theorem minimals_inter_subset : Minimals r s ∩ t ⊆ Minimals r (s ∩ t) :=
  maximals_inter_subset

theorem inter_maximals_subset : s ∩ Maximals r t ⊆ Maximals r (s ∩ t) := fun a ha =>
  ⟨⟨ha.1, ha.2.1⟩, fun b hb => ha.2.2 hb.2⟩

theorem inter_minimals_subset : s ∩ Minimals r t ⊆ Minimals r (s ∩ t) :=
  inter_maximals_subset

theorem _root_.is_antichain.maximals_eq (h : IsAntichain r s) : Maximals r s = s :=
  (maximals_subset _ _).antisymm fun a ha =>
    ⟨ha, fun b hb hab => by
      have := h.eq ha hb hab
      subst this
      exact hab⟩

theorem _root_.is_antichain.minimals_eq (h : IsAntichain r s) : Minimals r s = s :=
  (minimals_subset _ _).antisymm fun a ha =>
    ⟨ha, fun b hb hab => by
      have := h.eq hb ha hab
      subst this
      exact hab⟩

@[simp]
theorem maximals_idem : Maximals r (Maximals r s) = Maximals r s :=
  (maximals_subset _ _).antisymm fun a ha => ⟨ha, fun b hb => ha.2 hb.1⟩

@[simp]
theorem minimals_idem : Minimals r (Minimals r s) = Minimals r s :=
  maximals_idem

/-- If `maximals r s` is included in but *shadows* the antichain `t`, then it is actually
equal to `t`. -/
theorem IsAntichain.max_maximals (ht : IsAntichain r t) (h : Maximals r s ⊆ t)
    (hs : ∀ ⦃a⦄, a ∈ t → ∃ b ∈ Maximals r s, r b a) : Maximals r s = t := by
  refine' h.antisymm fun a ha => _
  obtain ⟨b, hb, hr⟩ := hs ha
  rwa [of_not_not fun hab => ht (h hb) ha (Ne.symm hab) hr]

/-- If `minimals r s` is included in but *shadows* the antichain `t`, then it is actually
equal to `t`. -/
theorem IsAntichain.max_minimals (ht : IsAntichain r t) (h : Minimals r s ⊆ t)
    (hs : ∀ ⦃a⦄, a ∈ t → ∃ b ∈ Minimals r s, r a b) : Minimals r s = t := by
  refine' h.antisymm fun a ha => _
  obtain ⟨b, hb, hr⟩ := hs ha
  rwa [of_not_not fun hab => ht ha (h hb) hab hr]

variable [PartialOrderₓ α]

theorem IsLeast.mem_minimals (h : IsLeast s a) : a ∈ Minimals (· ≤ ·) s :=
  ⟨h.1, fun b hb _ => h.2 hb⟩

theorem IsGreatest.mem_maximals (h : IsGreatest s a) : a ∈ Maximals (· ≤ ·) s :=
  ⟨h.1, fun b hb _ => h.2 hb⟩

theorem IsLeast.minimals_eq (h : IsLeast s a) : Minimals (· ≤ ·) s = {a} :=
  eq_singleton_iff_unique_mem.2 ⟨h.mem_minimals, fun b hb => eq_of_mem_minimals hb h.1 <| h.2 hb.1⟩

theorem IsGreatest.maximals_eq (h : IsGreatest s a) : Maximals (· ≤ ·) s = {a} :=
  eq_singleton_iff_unique_mem.2 ⟨h.mem_maximals, fun b hb => eq_of_mem_maximals hb h.1 <| h.2 hb.1⟩

theorem IsAntichain.minimals_upper_closure (hs : IsAntichain (· ≤ ·) s) :
    Minimals (· ≤ ·) (upperClosure s : Set α) = s :=
  (hs.max_minimals fun a ⟨⟨b, hb, hba⟩, h⟩ => by
      rwa [eq_of_mem_minimals ‹a ∈ _› (subset_upper_closure hb) hba])
    fun a ha =>
    ⟨a,
      ⟨subset_upper_closure ha, fun b ⟨c, hc, hcb⟩ hba => by
        rwa [hs.eq' ha hc (hcb.trans hba)]⟩,
      le_rflₓ⟩

theorem IsAntichain.maximals_lower_closure (hs : IsAntichain (· ≤ ·) s) :
    Maximals (· ≤ ·) (lowerClosure s : Set α) = s :=
  hs.toDual.minimals_upper_closure

