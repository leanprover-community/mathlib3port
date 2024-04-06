/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Data.ZMod.Defs
import SetTheory.Cardinal.Basic

#align_import set_theory.cardinal.finite from "leanprover-community/mathlib"@"3ff3f2d6a3118b8711063de7111a0d77a53219a8"

/-!
# Finite Cardinality Functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main Definitions

* `nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `nat.card α = 0`.
* `part_enat.card α` is the cardinality of `α` as an extended natural number
  (`part ℕ` implementation). If `α` is infinite, `part_enat.card α = ⊤`.
-/


open Cardinal

noncomputable section

open scoped BigOperators

variable {α β : Type _}

namespace Nat

#print Nat.card /-
/-- `nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `nat.card α = 0`. -/
protected def card (α : Type _) : ℕ :=
  (mk α).toNat
#align nat.card Nat.card
-/

#print Nat.card_eq_fintype_card /-
@[simp]
theorem card_eq_fintype_card [Fintype α] : Nat.card α = Fintype.card α :=
  mk_toNat_eq_card
#align nat.card_eq_fintype_card Nat.card_eq_fintype_card
-/

#print Nat.card_eq_zero_of_infinite /-
@[simp]
theorem card_eq_zero_of_infinite [Infinite α] : Nat.card α = 0 :=
  mk_toNat_of_infinite
#align nat.card_eq_zero_of_infinite Nat.card_eq_zero_of_infinite
-/

#print Nat.finite_of_card_ne_zero /-
theorem finite_of_card_ne_zero (h : Nat.card α ≠ 0) : Finite α :=
  not_infinite_iff_finite.mp <| h ∘ @Nat.card_eq_zero_of_infinite α
#align nat.finite_of_card_ne_zero Nat.finite_of_card_ne_zero
-/

#print Nat.card_congr /-
theorem card_congr (f : α ≃ β) : Nat.card α = Nat.card β :=
  Cardinal.toNat_congr f
#align nat.card_congr Nat.card_congr
-/

#print Nat.card_eq_of_bijective /-
theorem card_eq_of_bijective (f : α → β) (hf : Function.Bijective f) : Nat.card α = Nat.card β :=
  card_congr (Equiv.ofBijective f hf)
#align nat.card_eq_of_bijective Nat.card_eq_of_bijective
-/

#print Nat.card_eq_of_equiv_fin /-
theorem card_eq_of_equiv_fin {α : Type _} {n : ℕ} (f : α ≃ Fin n) : Nat.card α = n := by
  simpa using card_congr f
#align nat.card_eq_of_equiv_fin Nat.card_eq_of_equiv_fin
-/

#print Nat.equivFinOfCardPos /-
/-- If the cardinality is positive, that means it is a finite type, so there is
an equivalence between `α` and `fin (nat.card α)`. See also `finite.equiv_fin`. -/
def equivFinOfCardPos {α : Type _} (h : Nat.card α ≠ 0) : α ≃ Fin (Nat.card α) :=
  by
  cases fintypeOrInfinite α
  · simpa using Fintype.equivFin α
  · simpa using h
#align nat.equiv_fin_of_card_pos Nat.equivFinOfCardPos
-/

#print Nat.card_of_subsingleton /-
theorem card_of_subsingleton (a : α) [Subsingleton α] : Nat.card α = 1 :=
  by
  letI := Fintype.ofSubsingleton a
  rw [card_eq_fintype_card, Fintype.card_ofSubsingleton a]
#align nat.card_of_subsingleton Nat.card_of_subsingleton
-/

#print Nat.card_unique /-
@[simp]
theorem card_unique [Unique α] : Nat.card α = 1 :=
  card_of_subsingleton default
#align nat.card_unique Nat.card_unique
-/

#print Nat.card_eq_one_iff_unique /-
theorem card_eq_one_iff_unique : Nat.card α = 1 ↔ Subsingleton α ∧ Nonempty α :=
  Cardinal.toNat_eq_one_iff_unique
#align nat.card_eq_one_iff_unique Nat.card_eq_one_iff_unique
-/

#print Nat.card_eq_two_iff /-
theorem card_eq_two_iff : Nat.card α = 2 ↔ ∃ x y : α, x ≠ y ∧ {x, y} = @Set.univ α :=
  (toNat_eq_iff two_ne_zero).trans <| Iff.trans (by rw [Nat.cast_two]) mk_eq_two_iff
#align nat.card_eq_two_iff Nat.card_eq_two_iff
-/

#print Nat.card_eq_two_iff' /-
theorem card_eq_two_iff' (x : α) : Nat.card α = 2 ↔ ∃! y, y ≠ x :=
  (toNat_eq_iff two_ne_zero).trans <| Iff.trans (by rw [Nat.cast_two]) (mk_eq_two_iff' x)
#align nat.card_eq_two_iff' Nat.card_eq_two_iff'
-/

#print Nat.card_of_isEmpty /-
theorem card_of_isEmpty [IsEmpty α] : Nat.card α = 0 := by simp
#align nat.card_of_is_empty Nat.card_of_isEmpty
-/

#print Nat.card_prod /-
@[simp]
theorem card_prod (α β : Type _) : Nat.card (α × β) = Nat.card α * Nat.card β := by
  simp only [Nat.card, mk_prod, to_nat_mul, to_nat_lift]
#align nat.card_prod Nat.card_prod
-/

#print Nat.card_ulift /-
@[simp]
theorem card_ulift (α : Type _) : Nat.card (ULift α) = Nat.card α :=
  card_congr Equiv.ulift
#align nat.card_ulift Nat.card_ulift
-/

#print Nat.card_plift /-
@[simp]
theorem card_plift (α : Type _) : Nat.card (PLift α) = Nat.card α :=
  card_congr Equiv.plift
#align nat.card_plift Nat.card_plift
-/

#print Nat.card_pi /-
theorem card_pi {β : α → Type _} [Fintype α] : Nat.card (∀ a, β a) = ∏ a, Nat.card (β a) := by
  simp_rw [Nat.card, mk_pi, prod_eq_of_fintype, to_nat_lift, to_nat_finset_prod]
#align nat.card_pi Nat.card_pi
-/

#print Nat.card_fun /-
theorem card_fun [Finite α] : Nat.card (α → β) = Nat.card β ^ Nat.card α :=
  by
  haveI := Fintype.ofFinite α
  rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
#align nat.card_fun Nat.card_fun
-/

#print Nat.card_zmod /-
@[simp]
theorem card_zmod (n : ℕ) : Nat.card (ZMod n) = n :=
  by
  cases n
  · exact Nat.card_eq_zero_of_infinite
  · rw [Nat.card_eq_fintype_card, ZMod.card]
#align nat.card_zmod Nat.card_zmod
-/

end Nat

namespace PartENat

#print PartENat.card /-
/-- `part_enat.card α` is the cardinality of `α` as an extended natural number.
  If `α` is infinite, `part_enat.card α = ⊤`. -/
def card (α : Type _) : PartENat :=
  (mk α).toPartENat
#align part_enat.card PartENat.card
-/

#print PartENat.card_eq_coe_fintype_card /-
@[simp]
theorem card_eq_coe_fintype_card [Fintype α] : card α = Fintype.card α :=
  mk_toPartENat_eq_coe_card
#align part_enat.card_eq_coe_fintype_card PartENat.card_eq_coe_fintype_card
-/

#print PartENat.card_eq_top_of_infinite /-
@[simp]
theorem card_eq_top_of_infinite [Infinite α] : card α = ⊤ :=
  mk_toPartENat_of_infinite
#align part_enat.card_eq_top_of_infinite PartENat.card_eq_top_of_infinite
-/

#print PartENat.card_congr /-
theorem card_congr {α : Type _} {β : Type _} (f : α ≃ β) : PartENat.card α = PartENat.card β :=
  Cardinal.toPartENat_congr f
#align part_enat.card_congr PartENat.card_congr
-/

#print PartENat.card_ulift /-
theorem card_ulift (α : Type _) : card (ULift α) = card α :=
  card_congr Equiv.ulift
#align part_enat.card_ulift PartENat.card_ulift
-/

#print PartENat.card_plift /-
@[simp]
theorem card_plift (α : Type _) : card (PLift α) = card α :=
  card_congr Equiv.plift
#align part_enat.card_plift PartENat.card_plift
-/

#print PartENat.card_image_of_injOn /-
theorem card_image_of_injOn {α : Type _} {β : Type _} {f : α → β} {s : Set α} (h : Set.InjOn f s) :
    card (f '' s) = card s :=
  card_congr (Equiv.Set.imageOfInjOn f s h).symm
#align part_enat.card_image_of_inj_on PartENat.card_image_of_injOn
-/

#print PartENat.card_image_of_injective /-
theorem card_image_of_injective {α : Type _} {β : Type _} (f : α → β) (s : Set α)
    (h : Function.Injective f) : card (f '' s) = card s :=
  card_image_of_injOn (Set.injOn_of_injective h s)
#align part_enat.card_image_of_injective PartENat.card_image_of_injective
-/

#print Cardinal.natCast_le_toPartENat_iff /-
-- Should I keep the 6 following lemmas ?
@[simp]
theorem Cardinal.natCast_le_toPartENat_iff {n : ℕ} {c : Cardinal} : ↑n ≤ toPartENat c ↔ ↑n ≤ c := by
  rw [← to_part_enat_cast n, Cardinal.toPartENat_le_iff_of_le_aleph0 (le_of_lt (nat_lt_aleph_0 n))]
#align cardinal.coe_nat_le_to_part_enat_iff Cardinal.natCast_le_toPartENat_iff
-/

#print Cardinal.toPartENat_le_natCast_iff /-
@[simp]
theorem Cardinal.toPartENat_le_natCast_iff {c : Cardinal} {n : ℕ} : toPartENat c ≤ n ↔ c ≤ n := by
  rw [← to_part_enat_cast n, Cardinal.toPartENat_le_iff_of_lt_aleph0 (nat_lt_aleph_0 n)]
#align cardinal.to_part_enat_le_coe_nat_iff Cardinal.toPartENat_le_natCast_iff
-/

#print Cardinal.natCast_eq_toPartENat_iff /-
@[simp]
theorem Cardinal.natCast_eq_toPartENat_iff {n : ℕ} {c : Cardinal} : ↑n = toPartENat c ↔ ↑n = c := by
  rw [le_antisymm_iff, le_antisymm_iff, Cardinal.natCast_le_toPartENat_iff,
    Cardinal.toPartENat_le_natCast_iff]
#align cardinal.coe_nat_eq_to_part_enat_iff Cardinal.natCast_eq_toPartENat_iff
-/

@[simp]
theorem Cardinal.toPartENat_eq_coe_nat_iff {c : Cardinal} {n : ℕ} : toPartENat c = n ↔ c = n := by
  rw [eq_comm, Cardinal.natCast_eq_toPartENat_iff, eq_comm]
#align cardinal.to_part_enat_eq_coe_nat_iff Cardinal.toPartENat_eq_coe_nat_iff

@[simp]
theorem Cardinal.coe_nat_lt_coe_iff_lt {n : ℕ} {c : Cardinal} : ↑n < toPartENat c ↔ ↑n < c := by
  simp only [← not_le, Cardinal.toPartENat_le_natCast_iff]
#align cardinal.coe_nat_lt_coe_iff_lt Cardinal.coe_nat_lt_coe_iff_lt

@[simp]
theorem Cardinal.lt_coe_nat_iff_lt {n : ℕ} {c : Cardinal} : toPartENat c < n ↔ c < n := by
  simp only [← not_le, Cardinal.natCast_le_toPartENat_iff]
#align cardinal.lt_coe_nat_iff_lt Cardinal.lt_coe_nat_iff_lt

#print PartENat.card_eq_zero_iff_empty /-
theorem card_eq_zero_iff_empty (α : Type _) : card α = 0 ↔ IsEmpty α :=
  by
  rw [← Cardinal.mk_eq_zero_iff]
  conv_rhs => rw [← Nat.cast_zero]
  rw [← Cardinal.toPartENat_eq_coe_nat_iff]
  simp only [PartENat.card, Nat.cast_zero]
#align part_enat.card_eq_zero_iff_empty PartENat.card_eq_zero_iff_empty
-/

#print PartENat.card_le_one_iff_subsingleton /-
theorem card_le_one_iff_subsingleton (α : Type _) : card α ≤ 1 ↔ Subsingleton α :=
  by
  rw [← le_one_iff_subsingleton]
  conv_rhs => rw [← Nat.cast_one]
  rw [← Cardinal.toPartENat_le_natCast_iff]
  simp only [PartENat.card, Nat.cast_one]
#align part_enat.card_le_one_iff_subsingleton PartENat.card_le_one_iff_subsingleton
-/

#print PartENat.one_lt_card_iff_nontrivial /-
theorem one_lt_card_iff_nontrivial (α : Type _) : 1 < card α ↔ Nontrivial α :=
  by
  rw [← one_lt_iff_nontrivial]
  conv_rhs => rw [← Nat.cast_one]
  rw [← Cardinal.coe_nat_lt_coe_iff_lt]
  simp only [PartENat.card, Nat.cast_one]
#align part_enat.one_lt_card_iff_nontrivial PartENat.one_lt_card_iff_nontrivial
-/

theorem is_finite_of_card {α : Type _} {n : ℕ} (hα : PartENat.card α = n) : Finite α :=
  by
  apply Or.resolve_right (finite_or_infinite α)
  intro h; skip
  apply PartENat.natCast_ne_top n
  rw [← hα]
  exact PartENat.card_eq_top_of_infinite
#align part_enat.is_finite_of_card PartENat.is_finite_of_card

end PartENat

