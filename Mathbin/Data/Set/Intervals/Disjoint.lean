/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov
-/
import Mathbin.Data.Set.Lattice

/-!
# Extra lemmas about intervals

This file contains lemmas about intervals that cannot be included into `data.set.intervals.basic`
because this would create an `import` cycle. Namely, lemmas in this file can use definitions
from `data.set.lattice`, including `disjoint`.
-/


universe u v w

variable {ι : Sort u} {α : Type v} {β : Type w}

open Set

open OrderDual (toDual)

namespace Set

section Preorder

variable [Preorder α] {a b c : α}

@[simp]
theorem iicDisjointIoi (h : a ≤ b) : Disjoint (IicCat a) (IoiCat b) := fun x ⟨ha, hb⟩ => not_le_of_lt (h.trans_lt hb) ha

@[simp]
theorem iicDisjointIoc (h : a ≤ b) : Disjoint (IicCat a) (IocCat b c) :=
  (iicDisjointIoi h).mono le_rfl fun _ => And.left

@[simp]
theorem iocDisjointIocSame {a b c : α} : Disjoint (IocCat a b) (IocCat b c) :=
  (iicDisjointIoc (le_refl b)).mono (fun _ => And.right) le_rfl

@[simp]
theorem icoDisjointIcoSame {a b c : α} : Disjoint (IcoCat a b) (IcoCat b c) := fun x hx => not_le_of_lt hx.1.2 hx.2.1

@[simp]
theorem Ici_disjoint_Iic : Disjoint (IciCat a) (IicCat b) ↔ ¬a ≤ b := by
  rw [Set.disjoint_iff_inter_eq_empty, Ici_inter_Iic, Icc_eq_empty_iff]

@[simp]
theorem Iic_disjoint_Ici : Disjoint (IicCat a) (IciCat b) ↔ ¬b ≤ a :=
  Disjoint.comm.trans Ici_disjoint_Iic

@[simp]
theorem Union_Iic : (⋃ a : α, IicCat a) = univ :=
  Union_eq_univ_iff.2 fun x => ⟨x, right_mem_Iic⟩

@[simp]
theorem Union_Ici : (⋃ a : α, IciCat a) = univ :=
  Union_eq_univ_iff.2 fun x => ⟨x, left_mem_Ici⟩

@[simp]
theorem Union_Icc_right (a : α) : (⋃ b, IccCat a b) = IciCat a := by
  simp only [← Ici_inter_Iic, ← inter_Union, Union_Iic, inter_univ]

@[simp]
theorem Union_Ioc_right (a : α) : (⋃ b, IocCat a b) = IoiCat a := by
  simp only [← Ioi_inter_Iic, ← inter_Union, Union_Iic, inter_univ]

@[simp]
theorem Union_Icc_left (b : α) : (⋃ a, IccCat a b) = IicCat b := by
  simp only [← Ici_inter_Iic, ← Union_inter, Union_Ici, univ_inter]

@[simp]
theorem Union_Ico_left (b : α) : (⋃ a, IcoCat a b) = IioCat b := by
  simp only [← Ici_inter_Iio, ← Union_inter, Union_Ici, univ_inter]

@[simp]
theorem Union_Iio [NoMaxOrder α] : (⋃ a : α, IioCat a) = univ :=
  Union_eq_univ_iff.2 exists_gt

@[simp]
theorem Union_Ioi [NoMinOrder α] : (⋃ a : α, IoiCat a) = univ :=
  Union_eq_univ_iff.2 exists_lt

@[simp]
theorem Union_Ico_right [NoMaxOrder α] (a : α) : (⋃ b, IcoCat a b) = IciCat a := by
  simp only [← Ici_inter_Iio, ← inter_Union, Union_Iio, inter_univ]

@[simp]
theorem Union_Ioo_right [NoMaxOrder α] (a : α) : (⋃ b, IooCat a b) = IoiCat a := by
  simp only [← Ioi_inter_Iio, ← inter_Union, Union_Iio, inter_univ]

@[simp]
theorem Union_Ioc_left [NoMinOrder α] (b : α) : (⋃ a, IocCat a b) = IicCat b := by
  simp only [← Ioi_inter_Iic, ← Union_inter, Union_Ioi, univ_inter]

@[simp]
theorem Union_Ioo_left [NoMinOrder α] (b : α) : (⋃ a, IooCat a b) = IioCat b := by
  simp only [← Ioi_inter_Iio, ← Union_inter, Union_Ioi, univ_inter]

end Preorder

section LinearOrder

variable [LinearOrder α] {a₁ a₂ b₁ b₂ : α}

@[simp]
theorem Ico_disjoint_Ico : Disjoint (IcoCat a₁ a₂) (IcoCat b₁ b₂) ↔ min a₂ b₂ ≤ max a₁ b₁ := by
  simp_rw [Set.disjoint_iff_inter_eq_empty, Ico_inter_Ico, Ico_eq_empty_iff, inf_eq_min, sup_eq_max, not_lt]

@[simp]
theorem Ioc_disjoint_Ioc : Disjoint (IocCat a₁ a₂) (IocCat b₁ b₂) ↔ min a₂ b₂ ≤ max a₁ b₁ := by
  have h : _ ↔ min (toDual a₁) (toDual b₁) ≤ max (toDual a₂) (toDual b₂) := Ico_disjoint_Ico
  simpa only [dual_Ico] using h

/-- If two half-open intervals are disjoint and the endpoint of one lies in the other,
  then it must be equal to the endpoint of the other. -/
theorem eq_of_Ico_disjoint {x₁ x₂ y₁ y₂ : α} (h : Disjoint (IcoCat x₁ x₂) (IcoCat y₁ y₂)) (hx : x₁ < x₂)
    (h2 : x₂ ∈ IcoCat y₁ y₂) : y₁ = x₂ := by
  rw [Ico_disjoint_Ico, min_eq_left (le_of_lt h2.2), le_max_iff] at h
  apply le_antisymm h2.1
  exact h.elim (fun h => absurd hx (not_lt_of_le h)) id

@[simp]
theorem Union_Ico_eq_Iio_self_iff {f : ι → α} {a : α} : (⋃ i, IcoCat (f i) a) = IioCat a ↔ ∀ x < a, ∃ i, f i ≤ x := by
  simp [← Ici_inter_Iio, ← Union_inter, subset_def]

@[simp]
theorem Union_Ioc_eq_Ioi_self_iff {f : ι → α} {a : α} : (⋃ i, IocCat a (f i)) = IoiCat a ↔ ∀ x, a < x → ∃ i, x ≤ f i :=
  by simp [← Ioi_inter_Iic, ← inter_Union, subset_def]

@[simp]
theorem bUnion_Ico_eq_Iio_self_iff {p : ι → Prop} {f : ∀ i, p i → α} {a : α} :
    (⋃ (i) (hi : p i), IcoCat (f i hi) a) = IioCat a ↔ ∀ x < a, ∃ i hi, f i hi ≤ x := by
  simp [← Ici_inter_Iio, ← Union_inter, subset_def]

@[simp]
theorem bUnion_Ioc_eq_Ioi_self_iff {p : ι → Prop} {f : ∀ i, p i → α} {a : α} :
    (⋃ (i) (hi : p i), IocCat a (f i hi)) = IoiCat a ↔ ∀ x, a < x → ∃ i hi, x ≤ f i hi := by
  simp [← Ioi_inter_Iic, ← inter_Union, subset_def]

end LinearOrder

end Set

section UnionIxx

variable [LinearOrder α] {s : Set α} {a : α} {f : ι → α}

theorem IsGlb.bUnion_Ioi_eq (h : IsGlb s a) : (⋃ x ∈ s, IoiCat x) = IoiCat a := by
  refine' (Union₂_subset fun x hx => _).antisymm fun x hx => _
  · exact Ioi_subset_Ioi (h.1 hx)
    
  · rcases h.exists_between hx with ⟨y, hys, hay, hyx⟩
    exact mem_bUnion hys hyx
    

theorem IsGlb.Union_Ioi_eq (h : IsGlb (Range f) a) : (⋃ x, IoiCat (f x)) = IoiCat a :=
  bUnion_range.symm.trans h.bUnion_Ioi_eq

theorem IsLub.bUnion_Iio_eq (h : IsLub s a) : (⋃ x ∈ s, IioCat x) = IioCat a :=
  h.dual.bUnion_Ioi_eq

theorem IsLub.Union_Iio_eq (h : IsLub (Range f) a) : (⋃ x, IioCat (f x)) = IioCat a :=
  h.dual.Union_Ioi_eq

end UnionIxx

