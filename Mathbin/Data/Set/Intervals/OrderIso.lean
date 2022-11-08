/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov, Rémy Degenne
-/
import Mathbin.Data.Set.Intervals.Basic
import Mathbin.Order.Hom.Basic

/-!
# Lemmas about images of intervals under order isomorphisms.
-/


variable {α β : Type _}

open Set

namespace OrderIso

section Preorder

variable [Preorder α] [Preorder β]

@[simp]
theorem preimage_Iic (e : α ≃o β) (b : β) : e ⁻¹' IicCat b = IicCat (e.symm b) := by
  ext x
  simp [← e.le_iff_le]

@[simp]
theorem preimage_Ici (e : α ≃o β) (b : β) : e ⁻¹' IciCat b = IciCat (e.symm b) := by
  ext x
  simp [← e.le_iff_le]

@[simp]
theorem preimage_Iio (e : α ≃o β) (b : β) : e ⁻¹' IioCat b = IioCat (e.symm b) := by
  ext x
  simp [← e.lt_iff_lt]

@[simp]
theorem preimage_Ioi (e : α ≃o β) (b : β) : e ⁻¹' IoiCat b = IoiCat (e.symm b) := by
  ext x
  simp [← e.lt_iff_lt]

@[simp]
theorem preimage_Icc (e : α ≃o β) (a b : β) : e ⁻¹' IccCat a b = IccCat (e.symm a) (e.symm b) := by
  simp [← Ici_inter_Iic]

@[simp]
theorem preimage_Ico (e : α ≃o β) (a b : β) : e ⁻¹' IcoCat a b = IcoCat (e.symm a) (e.symm b) := by
  simp [← Ici_inter_Iio]

@[simp]
theorem preimage_Ioc (e : α ≃o β) (a b : β) : e ⁻¹' IocCat a b = IocCat (e.symm a) (e.symm b) := by
  simp [← Ioi_inter_Iic]

@[simp]
theorem preimage_Ioo (e : α ≃o β) (a b : β) : e ⁻¹' IooCat a b = IooCat (e.symm a) (e.symm b) := by
  simp [← Ioi_inter_Iio]

@[simp]
theorem image_Iic (e : α ≃o β) (a : α) : e '' IicCat a = IicCat (e a) := by
  rw [e.image_eq_preimage, e.symm.preimage_Iic, e.symm_symm]

@[simp]
theorem image_Ici (e : α ≃o β) (a : α) : e '' IciCat a = IciCat (e a) :=
  e.dual.image_Iic a

@[simp]
theorem image_Iio (e : α ≃o β) (a : α) : e '' IioCat a = IioCat (e a) := by
  rw [e.image_eq_preimage, e.symm.preimage_Iio, e.symm_symm]

@[simp]
theorem image_Ioi (e : α ≃o β) (a : α) : e '' IoiCat a = IoiCat (e a) :=
  e.dual.image_Iio a

@[simp]
theorem image_Ioo (e : α ≃o β) (a b : α) : e '' IooCat a b = IooCat (e a) (e b) := by
  rw [e.image_eq_preimage, e.symm.preimage_Ioo, e.symm_symm]

@[simp]
theorem image_Ioc (e : α ≃o β) (a b : α) : e '' IocCat a b = IocCat (e a) (e b) := by
  rw [e.image_eq_preimage, e.symm.preimage_Ioc, e.symm_symm]

@[simp]
theorem image_Ico (e : α ≃o β) (a b : α) : e '' IcoCat a b = IcoCat (e a) (e b) := by
  rw [e.image_eq_preimage, e.symm.preimage_Ico, e.symm_symm]

@[simp]
theorem image_Icc (e : α ≃o β) (a b : α) : e '' IccCat a b = IccCat (e a) (e b) := by
  rw [e.image_eq_preimage, e.symm.preimage_Icc, e.symm_symm]

end Preorder

/-- Order isomorphism between `Iic (⊤ : α)` and `α` when `α` has a top element -/
def iicTop [Preorder α] [OrderTop α] : Set.IicCat (⊤ : α) ≃o α :=
  { @Equiv.subtypeUnivEquiv α (Set.IicCat (⊤ : α)) fun x => le_top with map_rel_iff' := fun x y => by rfl }

/-- Order isomorphism between `Ici (⊥ : α)` and `α` when `α` has a bottom element -/
def iciBot [Preorder α] [OrderBot α] : Set.IciCat (⊥ : α) ≃o α :=
  { @Equiv.subtypeUnivEquiv α (Set.IciCat (⊥ : α)) fun x => bot_le with map_rel_iff' := fun x y => by rfl }

end OrderIso

