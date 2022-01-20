import Mathbin.Data.Sum.Order
import Mathbin.Order.LocallyFinite

/-!
# Finite intervals in a disjoint union

This file provides the `locally_finite_order` instance for the disjoint sum of two orders.

## TODO

Do the same for the lexicographic sum of orders.
-/


open Function Sum

namespace Finset

variable {α₁ α₂ β₁ β₂ γ₁ γ₂ : Type _}

section SumLift₂

variable (f f₁ g₁ : α₁ → β₁ → Finset γ₁) (g f₂ g₂ : α₂ → β₂ → Finset γ₂)

/-- Lifts maps `α₁ → β₁ → finset γ₁` and `α₂ → β₂ → finset γ₂` to a map
`α₁ ⊕ α₂ → β₁ ⊕ β₂ → finset (γ₁ ⊕ γ₂)`. Could be generalized to `alternative` functors if we can
make sure to keep computability and universe polymorphism. -/
@[simp]
def sum_lift₂ : ∀ a : Sum α₁ α₂ b : Sum β₁ β₂, Finset (Sum γ₁ γ₂)
  | inl a, inl b => (f a b).map embedding.inl
  | inl a, inr b => ∅
  | inr a, inl b => ∅
  | inr a, inr b => (g a b).map embedding.inr

variable {f f₁ g₁ g f₂ g₂} {a : Sum α₁ α₂} {b : Sum β₁ β₂} {c : Sum γ₁ γ₂}

theorem mem_sum_lift₂ :
    c ∈ sum_lift₂ f g a b ↔
      (∃ a₁ b₁ c₁, a = inl a₁ ∧ b = inl b₁ ∧ c = inl c₁ ∧ c₁ ∈ f a₁ b₁) ∨
        ∃ a₂ b₂ c₂, a = inr a₂ ∧ b = inr b₂ ∧ c = inr c₂ ∧ c₂ ∈ g a₂ b₂ :=
  by
  constructor
  · cases a <;> cases b
    · rw [sum_lift₂, mem_map]
      rintro ⟨c, hc, rfl⟩
      exact Or.inl ⟨a, b, c, rfl, rfl, rfl, hc⟩
      
    · refine' fun h => (not_mem_empty _ h).elim
      
    · refine' fun h => (not_mem_empty _ h).elim
      
    · rw [sum_lift₂, mem_map]
      rintro ⟨c, hc, rfl⟩
      exact Or.inr ⟨a, b, c, rfl, rfl, rfl, hc⟩
      
    
  · rintro (⟨a, b, c, rfl, rfl, rfl, h⟩ | ⟨a, b, c, rfl, rfl, rfl, h⟩) <;> exact mem_map_of_mem _ h
    

theorem inl_mem_sum_lift₂ {c₁ : γ₁} : inl c₁ ∈ sum_lift₂ f g a b ↔ ∃ a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ c₁ ∈ f a₁ b₁ := by
  rw [mem_sum_lift₂, or_iff_left]
  simp only [exists_and_distrib_left, exists_eq_left']
  rintro ⟨_, _, c₂, _, _, h, _⟩
  exact inl_ne_inr h

theorem inr_mem_sum_lift₂ {c₂ : γ₂} : inr c₂ ∈ sum_lift₂ f g a b ↔ ∃ a₂ b₂, a = inr a₂ ∧ b = inr b₂ ∧ c₂ ∈ g a₂ b₂ := by
  rw [mem_sum_lift₂, or_iff_right]
  simp only [exists_and_distrib_left, exists_eq_left']
  rintro ⟨_, _, c₂, _, _, h, _⟩
  exact inr_ne_inl h

theorem sum_lift₂_eq_empty :
    sum_lift₂ f g a b = ∅ ↔
      (∀ a₁ b₁, a = inl a₁ → b = inl b₁ → f a₁ b₁ = ∅) ∧ ∀ a₂ b₂, a = inr a₂ → b = inr b₂ → g a₂ b₂ = ∅ :=
  by
  refine' ⟨fun h => _, fun h => _⟩
  · constructor <;>
      · rintro a b rfl rfl
        exact map_eq_empty.1 h
        
    
  cases a <;> cases b
  · exact map_eq_empty.2 (h.1 _ _ rfl rfl)
    
  · rfl
    
  · rfl
    
  · exact map_eq_empty.2 (h.2 _ _ rfl rfl)
    

theorem sum_lift₂_nonempty :
    (sum_lift₂ f g a b).Nonempty ↔
      (∃ a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ (f a₁ b₁).Nonempty) ∨ ∃ a₂ b₂, a = inr a₂ ∧ b = inr b₂ ∧ (g a₂ b₂).Nonempty :=
  by
  simp [nonempty_iff_ne_empty, sum_lift₂_eq_empty, not_and_distrib]

theorem sum_lift₂_mono (h₁ : ∀ a b, f₁ a b ⊆ g₁ a b) (h₂ : ∀ a b, f₂ a b ⊆ g₂ a b) :
    ∀ a b, sum_lift₂ f₁ f₂ a b ⊆ sum_lift₂ g₁ g₂ a b
  | inl a, inl b => map_subset_map.2 (h₁ _ _)
  | inl a, inr b => subset.rfl
  | inr a, inl b => subset.rfl
  | inr a, inr b => map_subset_map.2 (h₂ _ _)

end SumLift₂

end Finset

open Finset Function

namespace Sum

variable {α β : Type _}

/-! ### Disjoint sum of orders -/


section Disjoint

variable [Preorderₓ α] [Preorderₓ β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]

instance : LocallyFiniteOrder (Sum α β) where
  finsetIcc := sum_lift₂ Icc Icc
  finsetIco := sum_lift₂ Ico Ico
  finsetIoc := sum_lift₂ Ioc Ioc
  finsetIoo := sum_lift₂ Ioo Ioo
  finset_mem_Icc := by
    rintro (a | a) (b | b) (x | x) <;> simp
  finset_mem_Ico := by
    rintro (a | a) (b | b) (x | x) <;> simp
  finset_mem_Ioc := by
    rintro (a | a) (b | b) (x | x) <;> simp
  finset_mem_Ioo := by
    rintro (a | a) (b | b) (x | x) <;> simp

variable (a₁ a₂ : α) (b₁ b₂ : β) (a b : Sum α β)

theorem Icc_inl_inl : Icc (inl a₁ : Sum α β) (inl a₂) = (Icc a₁ a₂).map embedding.inl :=
  rfl

theorem Ico_inl_inl : Ico (inl a₁ : Sum α β) (inl a₂) = (Ico a₁ a₂).map embedding.inl :=
  rfl

theorem Ioc_inl_inl : Ioc (inl a₁ : Sum α β) (inl a₂) = (Ioc a₁ a₂).map embedding.inl :=
  rfl

theorem Ioo_inl_inl : Ioo (inl a₁ : Sum α β) (inl a₂) = (Ioo a₁ a₂).map embedding.inl :=
  rfl

@[simp]
theorem Icc_inl_inr : Icc (inl a₁) (inr b₂) = ∅ :=
  rfl

@[simp]
theorem Ico_inl_inr : Ico (inl a₁) (inr b₂) = ∅ :=
  rfl

@[simp]
theorem Ioc_inl_inr : Ioc (inl a₁) (inr b₂) = ∅ :=
  rfl

@[simp]
theorem Ioo_inl_inr : Ioo (inl a₁) (inr b₂) = ∅ :=
  rfl

@[simp]
theorem Icc_inr_inl : Icc (inr b₁) (inl a₂) = ∅ :=
  rfl

@[simp]
theorem Ico_inr_inl : Ico (inr b₁) (inl a₂) = ∅ :=
  rfl

@[simp]
theorem Ioc_inr_inl : Ioc (inr b₁) (inl a₂) = ∅ :=
  rfl

@[simp]
theorem Ioo_inr_inl : Ioo (inr b₁) (inl a₂) = ∅ :=
  rfl

theorem Icc_inr_inr : Icc (inr b₁ : Sum α β) (inr b₂) = (Icc b₁ b₂).map embedding.inr :=
  rfl

theorem Ico_inr_inr : Ico (inr b₁ : Sum α β) (inr b₂) = (Ico b₁ b₂).map embedding.inr :=
  rfl

theorem Ioc_inr_inr : Ioc (inr b₁ : Sum α β) (inr b₂) = (Ioc b₁ b₂).map embedding.inr :=
  rfl

theorem Ioo_inr_inr : Ioo (inr b₁ : Sum α β) (inr b₂) = (Ioo b₁ b₂).map embedding.inr :=
  rfl

end Disjoint

end Sum

