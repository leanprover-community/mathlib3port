import Mathbin.Data.Finset.Lattice
import Mathbin.Logic.Function.Iterate

/-!
# Shadows

This file defines shadows of a set family. The shadow of a set family is the set family of sets we
get by removing any element from any set of the original family. If one pictures `finset α` as a big
hypercube (each dimension being membership of a given element), then taking the shadow corresponds
to projecting each finset down once in all available directions.

## Main definitions

The `shadow` of a set family is everything we can get by removing an element from each set.

## Notation

`∂ 𝒜` is notation for `shadow 𝒜`. It is situated in locale `finset_family`.

We also maintain the convention that `a, b : α` are elements of the ground type, `s, t : finset α`
are finsets, and `𝒜, ℬ : finset (finset α)` are finset families.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf
* http://discretemath.imp.fu-berlin.de/DMII-2015-16/kruskal.pdf

## Tags

shadow, set family
-/


open Finset Nat

variable {α : Type _}

namespace Finset

variable [DecidableEq α] {𝒜 : Finset (Finset α)} {s t : Finset α} {a : α} {k : ℕ}

/--  The shadow of a set family `𝒜` is all sets we can get by removing one element from any set in
`𝒜`, and the (`k` times) iterated shadow (`shadow^[k]`) is all sets we can get by removing `k`
elements from any set in `𝒜`. -/
def shadow (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  𝒜.sup fun s => s.image (erase s)

localized [FinsetFamily] notation:90 "∂ " => Finset.shadow

/--  The shadow of the empty set is empty. -/
@[simp]
theorem shadow_empty : (∂ ) (∅ : Finset (Finset α)) = ∅ :=
  rfl

/--  The shadow is monotone. -/
@[mono]
theorem shadow_monotone : Monotone (shadow : Finset (Finset α) → Finset (Finset α)) := fun 𝒜 ℬ => sup_mono

/--  `s` is in the shadow of `𝒜` iff there is an `t ∈ 𝒜` from which we can remove one element to
get `s`. -/
theorem mem_shadow_iff : s ∈ (∂ ) 𝒜 ↔ ∃ t ∈ 𝒜, ∃ a ∈ t, erase t a = s := by
  simp only [shadow, mem_sup, mem_image]

theorem erase_mem_shadow (hs : s ∈ 𝒜) (ha : a ∈ s) : erase s a ∈ (∂ ) 𝒜 :=
  mem_shadow_iff.2 ⟨s, hs, a, ha, rfl⟩

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (a «expr ∉ » s)
/--  `t` is in the shadow of `𝒜` iff we can add an element to it so that the resulting finset is in
`𝒜`. -/
theorem mem_shadow_iff_insert_mem : s ∈ (∂ ) 𝒜 ↔ ∃ (a : _)(_ : a ∉ s), insert a s ∈ 𝒜 := by
  refine' mem_shadow_iff.trans ⟨_, _⟩
  ·
    rintro ⟨s, hs, a, ha, rfl⟩
    refine' ⟨a, not_mem_erase a s, _⟩
    rwa [insert_erase ha]
  ·
    rintro ⟨a, ha, hs⟩
    exact ⟨insert a s, hs, a, mem_insert_self _ _, erase_insert ha⟩

/--  `s ∈ ∂ 𝒜` iff `s` is exactly one element less than something from `𝒜` -/
theorem mem_shadow_iff_exists_mem_card_add_one : s ∈ (∂ ) 𝒜 ↔ ∃ t ∈ 𝒜, s ⊆ t ∧ t.card = s.card+1 := by
  refine' mem_shadow_iff_insert_mem.trans ⟨_, _⟩
  ·
    rintro ⟨a, ha, hs⟩
    exact ⟨insert a s, hs, subset_insert _ _, card_insert_of_not_mem ha⟩
  ·
    rintro ⟨t, ht, hst, h⟩
    obtain ⟨a, ha⟩ : ∃ a, t \ s = {a} :=
      card_eq_one.1
        (by
          rw [card_sdiff hst, h, add_tsub_cancel_left])
    exact
      ⟨a, fun hat => not_mem_sdiff_of_mem_right hat ((ha.ge : _ ⊆ _) $ mem_singleton_self a), by
        rwa [insert_eq a s, ← ha, sdiff_union_of_subset hst]⟩

/--  Being in the shadow of `𝒜` means we have a superset in `𝒜`. -/
theorem exists_subset_of_mem_shadow (hs : s ∈ (∂ ) 𝒜) : ∃ t ∈ 𝒜, s ⊆ t :=
  let ⟨t, ht, hst⟩ := mem_shadow_iff_exists_mem_card_add_one.1 hs
  ⟨t, ht, hst.1⟩

/--  `t ∈ ∂^k 𝒜` iff `t` is exactly `k` elements less than something in `𝒜`. -/
theorem mem_shadow_iff_exists_mem_card_add : s ∈ (∂ ^[k]) 𝒜 ↔ ∃ t ∈ 𝒜, s ⊆ t ∧ t.card = s.card+k := by
  induction' k with k ih generalizing 𝒜 s
  ·
    refine' ⟨fun hs => ⟨s, hs, subset.refl _, rfl⟩, _⟩
    rintro ⟨t, ht, hst, hcard⟩
    rwa [eq_of_subset_of_card_le hst hcard.le]
  simp only [exists_prop, Function.comp_app, Function.iterate_succ]
  refine' ih.trans _
  clear ih
  constructor
  ·
    rintro ⟨t, ht, hst, hcardst⟩
    obtain ⟨u, hu, htu, hcardtu⟩ := mem_shadow_iff_exists_mem_card_add_one.1 ht
    refine' ⟨u, hu, hst.trans htu, _⟩
    rw [hcardtu, hcardst]
    rfl
  ·
    rintro ⟨t, ht, hst, hcard⟩
    obtain ⟨u, hsu, hut, hu⟩ :=
      Finset.exists_intermediate_set k
        (by
          rw [add_commₓ, hcard]
          exact le_succ _)
        hst
    rw [add_commₓ] at hu
    refine' ⟨u, mem_shadow_iff_exists_mem_card_add_one.2 ⟨t, ht, hut, _⟩, hsu, hu⟩
    rw [hcard, hu]
    rfl

end Finset

