/-
Copyright (c) 2022 Yaël Dillies, Ella Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Ella Yu
-/
import Data.Finset.Prod
import Data.Fintype.Prod

#align_import combinatorics.additive.energy from "leanprover-community/mathlib"@"327c3c0d9232d80e250dc8f65e7835b82b266ea5"

/-!
# Additive energy

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the additive energy of two finsets of a group. This is a central quantity in
additive combinatorics.

## TODO

It's possibly interesting to have
`(s ×ˢ s) ×ˢ t ×ˢ t).filter (λ x : (α × α) × α × α, x.1.1 * x.2.1 = x.1.2 * x.2.2)` (whose `card` is
`multiplicative_energy s t`) as a standalone definition.
-/


section

variable {α : Type _} [PartialOrder α] {x y : α}

end

variable {α : Type _} [DecidableEq α]

namespace Finset

section Mul

variable [Mul α] {s s₁ s₂ t t₁ t₂ : Finset α}

/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Finset.mulEnergy /-
/-- The multiplicative energy of two finsets `s` and `t` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`. -/
@[to_additive additive_energy
      "The additive energy of two finsets `s` and `t` in a group is the\nnumber of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`."]
def mulEnergy (s t : Finset α) : ℕ :=
  (((s ×ˢ s) ×ˢ t ×ˢ t).filterₓ fun x : (α × α) × α × α => x.1.1 * x.2.1 = x.1.2 * x.2.2).card
#align finset.multiplicative_energy Finset.mulEnergy
#align finset.additive_energy Finset.addEnergy
-/

#print Finset.mulEnergy_mono /-
@[to_additive additive_energy_mono]
theorem mulEnergy_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : mulEnergy s₁ t₁ ≤ mulEnergy s₂ t₂ :=
  card_le_card <|
    filter_subset_filter _ <|
      product_subset_product (product_subset_product hs hs) <| product_subset_product ht ht
#align finset.multiplicative_energy_mono Finset.mulEnergy_mono
#align finset.additive_energy_mono Finset.addEnergy_mono
-/

#print Finset.mulEnergy_mono_left /-
@[to_additive additive_energy_mono_left]
theorem mulEnergy_mono_left (hs : s₁ ⊆ s₂) : mulEnergy s₁ t ≤ mulEnergy s₂ t :=
  mulEnergy_mono hs Subset.rfl
#align finset.multiplicative_energy_mono_left Finset.mulEnergy_mono_left
#align finset.additive_energy_mono_left Finset.addEnergy_mono_left
-/

#print Finset.mulEnergy_mono_right /-
@[to_additive additive_energy_mono_right]
theorem mulEnergy_mono_right (ht : t₁ ⊆ t₂) : mulEnergy s t₁ ≤ mulEnergy s t₂ :=
  mulEnergy_mono Subset.rfl ht
#align finset.multiplicative_energy_mono_right Finset.mulEnergy_mono_right
#align finset.additive_energy_mono_right Finset.addEnergy_mono_right
-/

#print Finset.le_mulEnergy /-
@[to_additive le_additive_energy]
theorem le_mulEnergy : s.card * t.card ≤ mulEnergy s t :=
  by
  rw [← card_product]
  refine'
    card_le_card_of_inj_on (fun x => ((x.1, x.1), x.2, x.2)) (by simp [← and_imp]) fun a _ b _ => _
  simp only [Prod.mk.inj_iff, and_self_iff, and_imp]
  exact Prod.ext
#align finset.le_multiplicative_energy Finset.le_mulEnergy
#align finset.le_additive_energy Finset.le_addEnergy
-/

#print Finset.mulEnergy_pos /-
@[to_additive additive_energy_pos]
theorem mulEnergy_pos (hs : s.Nonempty) (ht : t.Nonempty) : 0 < mulEnergy s t :=
  (mul_pos hs.card_pos ht.card_pos).trans_le le_mulEnergy
#align finset.multiplicative_energy_pos Finset.mulEnergy_pos
#align finset.additive_energy_pos Finset.addEnergy_pos
-/

variable (s t)

#print Finset.mulEnergy_empty_left /-
@[simp, to_additive additive_energy_empty_left]
theorem mulEnergy_empty_left : mulEnergy ∅ t = 0 := by simp [multiplicative_energy]
#align finset.multiplicative_energy_empty_left Finset.mulEnergy_empty_left
#align finset.additive_energy_empty_left Finset.addEnergy_empty_left
-/

#print Finset.mulEnergy_empty_right /-
@[simp, to_additive additive_energy_empty_right]
theorem mulEnergy_empty_right : mulEnergy s ∅ = 0 := by simp [multiplicative_energy]
#align finset.multiplicative_energy_empty_right Finset.mulEnergy_empty_right
#align finset.additive_energy_empty_right Finset.addEnergy_empty_right
-/

variable {s t}

#print Finset.mulEnergy_pos_iff /-
@[simp, to_additive additive_energy_pos_iff]
theorem mulEnergy_pos_iff : 0 < mulEnergy s t ↔ s.Nonempty ∧ t.Nonempty :=
  ⟨fun h =>
    of_not_not fun H => by
      simp_rw [not_and_or, not_nonempty_iff_eq_empty] at H
      obtain rfl | rfl := H <;> simpa [Nat.not_lt_zero] using h,
    fun h => mulEnergy_pos h.1 h.2⟩
#align finset.multiplicative_energy_pos_iff Finset.mulEnergy_pos_iff
#align finset.additive_energy_pos_iff Finset.addEnergy_pos_iff
-/

#print Finset.mulEnergy_eq_zero_iff /-
@[simp, to_additive additive_energy_eq_zero_iff]
theorem mulEnergy_eq_zero_iff : mulEnergy s t = 0 ↔ s = ∅ ∨ t = ∅ := by
  simp [← (Nat.zero_le _).not_gt_iff_eq, not_and_or]
#align finset.multiplicative_energy_eq_zero_iff Finset.mulEnergy_eq_zero_iff
#align finset.additive_energy_eq_zero_iff Finset.addEnergy_eq_zero_iff
-/

end Mul

section CommMonoid

variable [CommMonoid α]

#print Finset.mulEnergy_comm /-
@[to_additive additive_energy_comm]
theorem mulEnergy_comm (s t : Finset α) : mulEnergy s t = mulEnergy t s :=
  by
  rw [multiplicative_energy, ← Finset.card_map (Equiv.prodComm _ _).toEmbedding, map_filter]
  simp [-Finset.card_map, eq_comm, multiplicative_energy, mul_comm, map_eq_image, Function.comp]
#align finset.multiplicative_energy_comm Finset.mulEnergy_comm
#align finset.additive_energy_comm Finset.addEnergy_comm
-/

end CommMonoid

section CommGroup

variable [CommGroup α] [Fintype α] (s t : Finset α)

/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Finset.mulEnergy_univ_left /-
@[simp, to_additive additive_energy_univ_left]
theorem mulEnergy_univ_left : mulEnergy univ t = Fintype.card α * t.card ^ 2 :=
  by
  simp only [multiplicative_energy, univ_product_univ, Fintype.card, sq, ← card_product]
  set f : α × α × α → (α × α) × α × α := fun x => ((x.1 * x.2.2, x.1 * x.2.1), x.2) with hf
  have : (↑((univ : Finset α) ×ˢ t ×ˢ t) : Set (α × α × α)).InjOn f :=
    by
    rintro ⟨a₁, b₁, c₁⟩ h₁ ⟨a₂, b₂, c₂⟩ h₂ h
    simp_rw [Prod.ext_iff] at h
    obtain ⟨h, rfl, rfl⟩ := h
    rw [mul_right_cancel h.1]
  rw [← card_image_of_inj_on this]
  congr with a
  simp only [hf, mem_filter, mem_product, mem_univ, true_and_iff, mem_image, exists_prop,
    Prod.exists]
  refine' ⟨fun h => ⟨a.1.1 * a.2.2⁻¹, _, _, h.1, by simp [mul_right_comm, h.2]⟩, _⟩
  rintro ⟨b, c, d, hcd, rfl⟩
  simpa [mul_right_comm]
#align finset.multiplicative_energy_univ_left Finset.mulEnergy_univ_left
#align finset.additive_energy_univ_left Finset.addEnergy_univ_left
-/

#print Finset.mulEnergy_univ_right /-
@[simp, to_additive additive_energy_univ_right]
theorem mulEnergy_univ_right : mulEnergy s univ = Fintype.card α * s.card ^ 2 := by
  rw [multiplicative_energy_comm, multiplicative_energy_univ_left]
#align finset.multiplicative_energy_univ_right Finset.mulEnergy_univ_right
#align finset.additive_energy_univ_right Finset.addEnergy_univ_right
-/

end CommGroup

end Finset

