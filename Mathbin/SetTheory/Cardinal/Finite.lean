/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.Data.Zmod.Defs
import Mathbin.SetTheory.Cardinal.Basic

/-!
# Finite Cardinality Functions

## Main Definitions

* `nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `nat.card α = 0`.
* `part_enat.card α` is the cardinality of `α` as an extended natural number
  (`part ℕ` implementation). If `α` is infinite, `part_enat.card α = ⊤`.
-/


open Cardinal

noncomputable section

open BigOperators

variable {α β : Type _}

namespace Nat

/-- `nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `nat.card α = 0`. -/
protected def card (α : Type _) : ℕ :=
  (mk α).toNat

@[simp]
theorem card_eq_fintype_card [Fintype α] : Nat.card α = Fintype.card α :=
  mk_to_nat_eq_card

@[simp]
theorem card_eq_zero_of_infinite [Infinite α] : Nat.card α = 0 :=
  mk_to_nat_of_infinite

theorem finite_of_card_ne_zero (h : Nat.card α ≠ 0) : Finite α :=
  not_infinite_iff_finite.mp <| h ∘ @Nat.card_eq_zero_of_infinite α

theorem card_congr (f : α ≃ β) : Nat.card α = Nat.card β :=
  Cardinal.to_nat_congr f

theorem card_eq_of_bijective (f : α → β) (hf : Function.Bijective f) : Nat.card α = Nat.card β :=
  card_congr (Equiv.ofBijective f hf)

theorem card_eq_of_equiv_fin {α : Type _} {n : ℕ} (f : α ≃ Fin n) : Nat.card α = n := by simpa using card_congr f

/-- If the cardinality is positive, that means it is a finite type, so there is
an equivalence between `α` and `fin (nat.card α)`. See also `finite.equiv_fin`. -/
def equivFinOfCardPos {α : Type _} (h : Nat.card α ≠ 0) : α ≃ Fin (Nat.card α) := by
  cases fintypeOrInfinite α
  · simpa using Fintype.equivFin α
    
  · simpa using h
    

theorem card_of_subsingleton (a : α) [Subsingleton α] : Nat.card α = 1 := by
  letI := Fintype.ofSubsingleton a
  rw [card_eq_fintype_card, Fintype.card_of_subsingleton a]

@[simp]
theorem card_unique [Unique α] : Nat.card α = 1 :=
  card_of_subsingleton default

theorem card_eq_one_iff_unique : Nat.card α = 1 ↔ Subsingleton α ∧ Nonempty α :=
  Cardinal.to_nat_eq_one_iff_unique

theorem card_eq_two_iff : Nat.card α = 2 ↔ ∃ x y : α, x ≠ y ∧ {x, y} = @Set.Univ α :=
  (to_nat_eq_iff two_ne_zero).trans <| Iff.trans (by rw [Nat.cast_two]) mk_eq_two_iff

theorem card_eq_two_iff' (x : α) : Nat.card α = 2 ↔ ∃! y, y ≠ x :=
  (to_nat_eq_iff two_ne_zero).trans <| Iff.trans (by rw [Nat.cast_two]) (mk_eq_two_iff' x)

theorem card_of_is_empty [IsEmpty α] : Nat.card α = 0 := by simp

@[simp]
theorem card_prod (α β : Type _) : Nat.card (α × β) = Nat.card α * Nat.card β := by
  simp only [Nat.card, mk_prod, to_nat_mul, to_nat_lift]

@[simp]
theorem card_ulift (α : Type _) : Nat.card (ULift α) = Nat.card α :=
  card_congr Equiv.ulift

@[simp]
theorem card_plift (α : Type _) : Nat.card (PLift α) = Nat.card α :=
  card_congr Equiv.plift

theorem card_pi {β : α → Type _} [Fintype α] : Nat.card (∀ a, β a) = ∏ a, Nat.card (β a) := by
  simp_rw [Nat.card, mk_pi, prod_eq_of_fintype, to_nat_lift, to_nat_finset_prod]

theorem card_fun [Finite α] : Nat.card (α → β) = Nat.card β ^ Nat.card α := by
  haveI := Fintype.ofFinite α
  rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card]

@[simp]
theorem card_zmod (n : ℕ) : Nat.card (Zmod n) = n := by
  cases n
  · exact Nat.card_eq_zero_of_infinite
    
  · rw [Nat.card_eq_fintype_card, Zmod.card]
    

end Nat

namespace PartEnat

/-- `part_enat.card α` is the cardinality of `α` as an extended natural number.
  If `α` is infinite, `part_enat.card α = ⊤`. -/
def card (α : Type _) : PartEnat :=
  (mk α).toPartEnat

@[simp]
theorem card_eq_coe_fintype_card [Fintype α] : card α = Fintype.card α :=
  mk_to_part_enat_eq_coe_card

@[simp]
theorem card_eq_top_of_infinite [Infinite α] : card α = ⊤ :=
  mk_to_part_enat_of_infinite

end PartEnat

