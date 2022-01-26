import Mathbin.Data.Multiset.Nodup

/-!
# Disjoint sum of multisets

This file defines the disjoint sum of two multisets as `multiset (α ⊕ β)`. Beware not to confuse
with the `multiset.sum` operation which computes the additive sum.

## Main declarations

* `multiset.disj_sum`: `s.disj_sum t` is the disjoint sum of `s` and `t`.
-/


open Sum

namespace Multiset

variable {α β : Type _} (s : Multiset α) (t : Multiset β)

/-- Disjoint sum of multisets. -/
def disj_sum : Multiset (Sum α β) :=
  s.map inl + t.map inr

@[simp]
theorem zero_disj_sum : (0 : Multiset α).disjSum t = t.map inr :=
  zero_addₓ _

@[simp]
theorem disj_sum_zero : s.disj_sum (0 : Multiset β) = s.map inl :=
  add_zeroₓ _

@[simp]
theorem card_disj_sum : (s.disj_sum t).card = s.card + t.card := by
  rw [disj_sum, card_add, card_map, card_map]

variable {s t} {s₁ s₂ : Multiset α} {t₁ t₂ : Multiset β} {a : α} {b : β} {x : Sum α β}

theorem mem_disj_sum : x ∈ s.disj_sum t ↔ (∃ a, a ∈ s ∧ inl a = x) ∨ ∃ b, b ∈ t ∧ inr b = x := by
  simp_rw [disj_sum, mem_add, mem_map]

@[simp]
theorem inl_mem_disj_sum : inl a ∈ s.disj_sum t ↔ a ∈ s := by
  rw [mem_disj_sum, or_iff_left]
  simp only [exists_eq_right]
  rintro ⟨b, _, hb⟩
  exact inr_ne_inl hb

@[simp]
theorem inr_mem_disj_sum : inr b ∈ s.disj_sum t ↔ b ∈ t := by
  rw [mem_disj_sum, or_iff_right]
  simp only [exists_eq_right]
  rintro ⟨a, _, ha⟩
  exact inl_ne_inr ha

theorem disj_sum_mono (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) : s₁.disj_sum t₁ ≤ s₂.disj_sum t₂ :=
  add_le_add (map_le_map hs) (map_le_map ht)

theorem disj_sum_mono_left (t : Multiset β) : Monotone fun s : Multiset α => s.disj_sum t := fun s₁ s₂ hs =>
  add_le_add_right (map_le_map hs) _

theorem disj_sum_mono_right (s : Multiset α) : Monotone (s.disj_sum : Multiset β → Multiset (Sum α β)) :=
  fun t₁ t₂ ht => add_le_add_left (map_le_map ht) _

theorem disj_sum_lt_disj_sum_of_lt_of_le (hs : s₁ < s₂) (ht : t₁ ≤ t₂) : s₁.disj_sum t₁ < s₂.disj_sum t₂ :=
  add_lt_add_of_lt_of_le (map_lt_map hs) (map_le_map ht)

theorem disj_sum_lt_disj_sum_of_le_of_lt (hs : s₁ ≤ s₂) (ht : t₁ < t₂) : s₁.disj_sum t₁ < s₂.disj_sum t₂ :=
  add_lt_add_of_le_of_lt (map_le_map hs) (map_lt_map ht)

theorem disj_sum_strict_mono_left (t : Multiset β) : StrictMono fun s : Multiset α => s.disj_sum t := fun s₁ s₂ hs =>
  disj_sum_lt_disj_sum_of_lt_of_le hs le_rfl

theorem disj_sum_strict_mono_right (s : Multiset α) : StrictMono (s.disj_sum : Multiset β → Multiset (Sum α β)) :=
  fun s₁ s₂ => disj_sum_lt_disj_sum_of_le_of_lt le_rfl

protected theorem nodup.disj_sum (hs : s.nodup) (ht : t.nodup) : (s.disj_sum t).Nodup := by
  refine'
    (Multiset.nodup_add_of_nodup (Multiset.nodup_map inl_injective hs) <| Multiset.nodup_map inr_injective ht).2
      fun x hs ht => _
  rw [Multiset.mem_map] at hs ht
  obtain ⟨a, _, rfl⟩ := hs
  obtain ⟨b, _, h⟩ := ht
  exact inr_ne_inl h

end Multiset

