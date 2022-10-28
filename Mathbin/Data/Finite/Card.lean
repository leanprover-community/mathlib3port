/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathbin.Data.Finite.Basic
import Mathbin.SetTheory.Cardinal.Finite

/-!

# Cardinality of finite types

The cardinality of a finite type `α` is given by `nat.card α`. This function has
the "junk value" of `0` for infinite types, but to ensure the function has valid
output, one just needs to know that it's possible to produce a `finite` instance
for the type. (Note: we could have defined a `finite.card` that required you to
supply a `finite` instance, but (a) the function would be `noncomputable` anyway
so there is no need to supply the instance and (b) the function would have a more
complicated dependent type that easily leads to "motive not type correct" errors.)

## Implementation notes

Theorems about `nat.card` are sometimes incidentally true for both finite and infinite
types. If removing a finiteness constraint results in no loss in legibility, we remove
it. We generally put such theorems into the `set_theory.cardinal.finite` module.

-/


noncomputable section

open Classical

variable {α β γ : Type _}

/-- There is (noncomputably) an equivalence between a finite type `α` and `fin (nat.card α)`. -/
def Finite.equivFin (α : Type _) [Finite α] : α ≃ Fin (Nat.card α) := by
  have := (Finite.exists_equiv_fin α).some_spec.some
  rwa [Nat.card_eq_of_equiv_fin this]

/-- Similar to `finite.equiv_fin` but with control over the term used for the cardinality. -/
def Finite.equivFinOfCardEq [Finite α] {n : ℕ} (h : Nat.card α = n) : α ≃ Fin n := by
  subst h
  apply Finite.equivFin

theorem Nat.card_eq (α : Type _) : Nat.card α = if h : Finite α then @Fintype.card α (Fintype.ofFinite α) else 0 := by
  cases finite_or_infinite α
  · letI := Fintype.ofFinite α
    simp only [*, Nat.card_eq_fintype_card, dif_pos]
    
  · simp [*, not_finite_iff_infinite.mpr h]
    

theorem Finite.card_pos_iff [Finite α] : 0 < Nat.card α ↔ Nonempty α := by
  haveI := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Fintype.card_pos_iff]

theorem Finite.card_pos [Finite α] [h : Nonempty α] : 0 < Nat.card α :=
  Finite.card_pos_iff.mpr h

namespace Finite

theorem card_eq [Finite α] [Finite β] : Nat.card α = Nat.card β ↔ Nonempty (α ≃ β) := by
  haveI := Fintype.ofFinite α
  haveI := Fintype.ofFinite β
  simp [Fintype.card_eq]

theorem card_le_one_iff_subsingleton [Finite α] : Nat.card α ≤ 1 ↔ Subsingleton α := by
  haveI := Fintype.ofFinite α
  simp [Fintype.card_le_one_iff_subsingleton]

theorem one_lt_card_iff_nontrivial [Finite α] : 1 < Nat.card α ↔ Nontrivial α := by
  haveI := Fintype.ofFinite α
  simp [Fintype.one_lt_card_iff_nontrivial]

theorem one_lt_card [Finite α] [h : Nontrivial α] : 1 < Nat.card α :=
  one_lt_card_iff_nontrivial.mpr h

@[simp]
theorem card_option [Finite α] : Nat.card (Option α) = Nat.card α + 1 := by
  haveI := Fintype.ofFinite α
  simp

theorem card_le_of_injective [Finite β] (f : α → β) (hf : Function.Injective f) : Nat.card α ≤ Nat.card β := by
  haveI := Fintype.ofFinite β
  haveI := Fintype.ofInjective f hf
  simpa using Fintype.card_le_of_injective f hf

theorem card_le_of_embedding [Finite β] (f : α ↪ β) : Nat.card α ≤ Nat.card β :=
  card_le_of_injective _ f.Injective

theorem card_le_of_surjective [Finite α] (f : α → β) (hf : Function.Surjective f) : Nat.card β ≤ Nat.card α := by
  haveI := Fintype.ofFinite α
  haveI := Fintype.ofSurjective f hf
  simpa using Fintype.card_le_of_surjective f hf

theorem card_eq_zero_iff [Finite α] : Nat.card α = 0 ↔ IsEmpty α := by
  haveI := Fintype.ofFinite α
  simp [Fintype.card_eq_zero_iff]

/-- If `f` is injective, then `nat.card α ≤ nat.card β`. We must also assume
  `nat.card β = 0 → nat.card α = 0` since `nat.card` is defined to be `0` for infinite types. -/
theorem card_le_of_injective' {f : α → β} (hf : Function.Injective f) (h : Nat.card β = 0 → Nat.card α = 0) :
    Nat.card α ≤ Nat.card β :=
  (or_not_of_imp h).casesOn (fun h => le_of_eq_of_le h zero_le') fun h =>
    @card_le_of_injective α β (Nat.finite_of_card_ne_zero h) f hf

/-- If `f` is an embedding, then `nat.card α ≤ nat.card β`. We must also assume
  `nat.card β = 0 → nat.card α = 0` since `nat.card` is defined to be `0` for infinite types. -/
theorem card_le_of_embedding' (f : α ↪ β) (h : Nat.card β = 0 → Nat.card α = 0) : Nat.card α ≤ Nat.card β :=
  card_le_of_injective' f.2 h

/-- If `f` is surjective, then `nat.card β ≤ nat.card α`. We must also assume
  `nat.card α = 0 → nat.card β = 0` since `nat.card` is defined to be `0` for infinite types. -/
theorem card_le_of_surjective' {f : α → β} (hf : Function.Surjective f) (h : Nat.card α = 0 → Nat.card β = 0) :
    Nat.card β ≤ Nat.card α :=
  (or_not_of_imp h).casesOn (fun h => le_of_eq_of_le h zero_le') fun h =>
    @card_le_of_surjective α β (Nat.finite_of_card_ne_zero h) f hf

/-- NB: `nat.card` is defined to be `0` for infinite types. -/
theorem card_eq_zero_of_surjective {f : α → β} (hf : Function.Surjective f) (h : Nat.card β = 0) : Nat.card α = 0 := by
  cases finite_or_infinite β
  · haveI := card_eq_zero_iff.mp h
    haveI := Function.is_empty f
    exact Nat.card_of_is_empty
    
  · haveI := Infinite.of_surjective f hf
    exact Nat.card_eq_zero_of_infinite
    

/-- NB: `nat.card` is defined to be `0` for infinite types. -/
theorem card_eq_zero_of_injective [Nonempty α] {f : α → β} (hf : Function.Injective f) (h : Nat.card α = 0) :
    Nat.card β = 0 :=
  card_eq_zero_of_surjective (Function.inv_fun_surjective hf) h

/-- NB: `nat.card` is defined to be `0` for infinite types. -/
theorem card_eq_zero_of_embedding [Nonempty α] (f : α ↪ β) (h : Nat.card α = 0) : Nat.card β = 0 :=
  card_eq_zero_of_injective f.2 h

theorem card_sum [Finite α] [Finite β] : Nat.card (Sum α β) = Nat.card α + Nat.card β := by
  haveI := Fintype.ofFinite α
  haveI := Fintype.ofFinite β
  simp

end Finite

theorem Finite.card_subtype_le [Finite α] (p : α → Prop) : Nat.card { x // p x } ≤ Nat.card α := by
  haveI := Fintype.ofFinite α
  simpa using Fintype.card_subtype_le p

theorem Finite.card_subtype_lt [Finite α] {p : α → Prop} {x : α} (hx : ¬p x) : Nat.card { x // p x } < Nat.card α := by
  haveI := Fintype.ofFinite α
  simpa using Fintype.card_subtype_lt hx

