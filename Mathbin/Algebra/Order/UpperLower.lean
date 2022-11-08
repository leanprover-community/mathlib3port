/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Algebra.Order.Group.Basic
import Mathbin.Data.Set.Pointwise.Basic
import Mathbin.Order.UpperLower

/-!
# Algebraic operations on upper/lower sets

Upper/lower sets are preserved under pointwise algebraic operations in ordered groups.
-/


open Function Set

open Pointwise

section OrderedCommMonoid

variable {α : Type _} [OrderedCommMonoid α] {s : Set α} {x : α}

@[to_additive]
theorem IsUpperSet.smul_subset (hs : IsUpperSet s) (hx : 1 ≤ x) : x • s ⊆ s :=
  smul_set_subset_iff.2 fun y => hs <| le_mul_of_one_le_left' hx

@[to_additive]
theorem IsLowerSet.smul_subset (hs : IsLowerSet s) (hx : x ≤ 1) : x • s ⊆ s :=
  smul_set_subset_iff.2 fun y => hs <| mul_le_of_le_one_left' hx

end OrderedCommMonoid

section OrderedCommGroup

variable {α : Type _} [OrderedCommGroup α] {s t : Set α} {a : α}

@[to_additive]
theorem IsUpperSet.smul (hs : IsUpperSet s) : IsUpperSet (a • s) := by
  rintro _ y hxy ⟨x, hx, rfl⟩
  exact mem_smul_set_iff_inv_smul_mem.2 (hs (le_inv_mul_iff_mul_le.2 hxy) hx)

@[to_additive]
theorem IsLowerSet.smul (hs : IsLowerSet s) : IsLowerSet (a • s) :=
  hs.ofDual.smul

@[to_additive]
theorem Set.OrdConnected.smul (hs : s.OrdConnected) : (a • s).OrdConnected := by
  rw [← hs.upper_closure_inter_lower_closure, smul_set_inter]
  exact (upperClosure _).upper.smul.OrdConnected.inter (lowerClosure _).lower.smul.OrdConnected

@[to_additive]
theorem IsUpperSet.mul_left (ht : IsUpperSet t) : IsUpperSet (s * t) := by
  rw [← smul_eq_mul, ← bUnion_smul_set]
  exact is_upper_set_Union₂ fun x hx => ht.smul

@[to_additive]
theorem IsUpperSet.mul_right (hs : IsUpperSet s) : IsUpperSet (s * t) := by
  rw [mul_comm]
  exact hs.mul_left

@[to_additive]
theorem IsLowerSet.mul_left (ht : IsLowerSet t) : IsLowerSet (s * t) :=
  ht.ofDual.mul_left

@[to_additive]
theorem IsLowerSet.mul_right (hs : IsLowerSet s) : IsLowerSet (s * t) :=
  hs.ofDual.mul_right

@[to_additive]
theorem IsUpperSet.inv (hs : IsUpperSet s) : IsLowerSet s⁻¹ := fun x y h => hs <| inv_le_inv' h

@[to_additive]
theorem IsLowerSet.inv (hs : IsLowerSet s) : IsUpperSet s⁻¹ := fun x y h => hs <| inv_le_inv' h

@[to_additive]
theorem IsUpperSet.div_left (ht : IsUpperSet t) : IsLowerSet (s / t) := by
  rw [div_eq_mul_inv]
  exact ht.inv.mul_left

@[to_additive]
theorem IsUpperSet.div_right (hs : IsUpperSet s) : IsUpperSet (s / t) := by
  rw [div_eq_mul_inv]
  exact hs.mul_right

@[to_additive]
theorem IsLowerSet.div_left (ht : IsLowerSet t) : IsUpperSet (s / t) :=
  ht.ofDual.div_left

@[to_additive]
theorem IsLowerSet.div_right (hs : IsLowerSet s) : IsLowerSet (s / t) :=
  hs.ofDual.div_right

namespace UpperSet

@[to_additive]
instance : One (UpperSet α) :=
  ⟨ici 1⟩

@[to_additive]
instance : Mul (UpperSet α) :=
  ⟨fun s t => ⟨Image2 (· * ·) s t, s.2.mul_right⟩⟩

@[to_additive]
instance : Div (UpperSet α) :=
  ⟨fun s t => ⟨Image2 (· / ·) s t, s.2.div_right⟩⟩

@[to_additive]
instance : HasSmul α (UpperSet α) :=
  ⟨fun a s => ⟨(· • ·) a '' s, s.2.smul⟩⟩

@[simp, norm_cast, to_additive]
theorem coe_one : ((1 : UpperSet α) : Set α) = Set.IciCat 1 :=
  rfl

@[simp, norm_cast, to_additive]
theorem coe_smul (a : α) (s : UpperSet α) : (↑(a • s) : Set α) = a • s :=
  rfl

@[simp, norm_cast, to_additive]
theorem coe_mul (s t : UpperSet α) : (↑(s * t) : Set α) = s * t :=
  rfl

@[simp, norm_cast, to_additive]
theorem coe_div (s t : UpperSet α) : (↑(s / t) : Set α) = s / t :=
  rfl

@[simp, to_additive]
theorem Ici_one : ici (1 : α) = 1 :=
  rfl

@[to_additive]
instance : MulAction α (UpperSet α) :=
  SetLike.coe_injective.MulAction _ coe_smul

@[to_additive]
instance : CommSemigroup (UpperSet α) :=
  { (SetLike.coe_injective.CommSemigroup _ coe_mul : CommSemigroup (UpperSet α)) with mul := (· * ·) }

@[to_additive]
private theorem one_mul (s : UpperSet α) : 1 * s = s :=
  SetLike.coe_injective <|
    (subset_mul_right _ left_mem_Ici).antisymm' <| by
      rw [← smul_eq_mul, ← bUnion_smul_set]
      exact Union₂_subset fun _ => s.upper.smul_subset

@[to_additive]
instance : CommMonoid (UpperSet α) :=
  { UpperSet.commSemigroup with one := 1, one_mul := one_mul,
    mul_one := fun s => by
      rw [mul_comm]
      exact one_mul _ }

end UpperSet

namespace LowerSet

@[to_additive]
instance : One (LowerSet α) :=
  ⟨iic 1⟩

@[to_additive]
instance : Mul (LowerSet α) :=
  ⟨fun s t => ⟨Image2 (· * ·) s t, s.2.mul_right⟩⟩

@[to_additive]
instance : Div (LowerSet α) :=
  ⟨fun s t => ⟨Image2 (· / ·) s t, s.2.div_right⟩⟩

@[to_additive]
instance : HasSmul α (LowerSet α) :=
  ⟨fun a s => ⟨(· • ·) a '' s, s.2.smul⟩⟩

@[simp, norm_cast, to_additive]
theorem coe_smul (a : α) (s : LowerSet α) : (↑(a • s) : Set α) = a • s :=
  rfl

@[simp, norm_cast, to_additive]
theorem coe_mul (s t : LowerSet α) : (↑(s * t) : Set α) = s * t :=
  rfl

@[simp, norm_cast, to_additive]
theorem coe_div (s t : LowerSet α) : (↑(s / t) : Set α) = s / t :=
  rfl

@[simp, to_additive]
theorem Iic_one : iic (1 : α) = 1 :=
  rfl

@[to_additive]
instance : MulAction α (LowerSet α) :=
  SetLike.coe_injective.MulAction _ coe_smul

@[to_additive]
instance : CommSemigroup (LowerSet α) :=
  { (SetLike.coe_injective.CommSemigroup _ coe_mul : CommSemigroup (LowerSet α)) with mul := (· * ·) }

@[to_additive]
private theorem one_mul (s : LowerSet α) : 1 * s = s :=
  SetLike.coe_injective <|
    (subset_mul_right _ right_mem_Iic).antisymm' <| by
      rw [← smul_eq_mul, ← bUnion_smul_set]
      exact Union₂_subset fun _ => s.lower.smul_subset

@[to_additive]
instance : CommMonoid (LowerSet α) :=
  { LowerSet.commSemigroup with one := 1, one_mul := one_mul,
    mul_one := fun s => by
      rw [mul_comm]
      exact one_mul _ }

end LowerSet

variable (a s t)

@[simp, to_additive]
theorem upper_closure_one : upperClosure (1 : Set α) = 1 :=
  upper_closure_singleton _

@[simp, to_additive]
theorem lower_closure_one : lowerClosure (1 : Set α) = 1 :=
  lower_closure_singleton _

@[simp, to_additive]
theorem upper_closure_smul : upperClosure (a • s) = a • upperClosure s :=
  upper_closure_image <| OrderIso.mulLeft a

@[simp, to_additive]
theorem lower_closure_smul : lowerClosure (a • s) = a • lowerClosure s :=
  lower_closure_image <| OrderIso.mulLeft a

@[to_additive]
theorem mul_upper_closure : s * upperClosure t = upperClosure (s * t) := by
  simp_rw [← smul_eq_mul, ← bUnion_smul_set, upper_closure_Union, upper_closure_smul, UpperSet.coe_infi₂,
    UpperSet.coe_smul]

@[to_additive]
theorem mul_lower_closure : s * lowerClosure t = lowerClosure (s * t) := by
  simp_rw [← smul_eq_mul, ← bUnion_smul_set, lower_closure_Union, lower_closure_smul, LowerSet.coe_supr₂,
    LowerSet.coe_smul]

@[to_additive]
theorem upper_closure_mul : ↑(upperClosure s) * t = upperClosure (s * t) := by
  simp_rw [mul_comm _ t]
  exact mul_upper_closure _ _

@[to_additive]
theorem lower_closure_mul : ↑(lowerClosure s) * t = lowerClosure (s * t) := by
  simp_rw [mul_comm _ t]
  exact mul_lower_closure _ _

@[simp, to_additive]
theorem upper_closure_mul_distrib : upperClosure (s * t) = upperClosure s * upperClosure t :=
  SetLike.coe_injective <| by rw [UpperSet.coe_mul, mul_upper_closure, upper_closure_mul, UpperSet.upper_closure]

@[simp, to_additive]
theorem lower_closure_mul_distrib : lowerClosure (s * t) = lowerClosure s * lowerClosure t :=
  SetLike.coe_injective <| by rw [LowerSet.coe_mul, mul_lower_closure, lower_closure_mul, LowerSet.lower_closure]

end OrderedCommGroup

