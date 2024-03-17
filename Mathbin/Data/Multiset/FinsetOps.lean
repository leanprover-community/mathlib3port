/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Data.Multiset.Dedup

#align_import data.multiset.finset_ops from "leanprover-community/mathlib"@"c227d107bbada5d0d9d20287e3282c0a7f1651a0"

/-!
# Preparations for defining operations on `finset`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The operations here ignore multiplicities,
and preparatory for defining the corresponding operations on `finset`.
-/


namespace Multiset

open List

variable {α : Type _} [DecidableEq α] {s : Multiset α}

/-! ### finset insert -/


#print Multiset.ndinsert /-
/-- `ndinsert a s` is the lift of the list `insert` operation. This operation
  does not respect multiplicities, unlike `cons`, but it is suitable as
  an insert operation on `finset`. -/
def ndinsert (a : α) (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => (l.insert a : Multiset α)) fun s t p => Quot.sound (p.insert a)
#align multiset.ndinsert Multiset.ndinsert
-/

#print Multiset.coe_ndinsert /-
@[simp]
theorem coe_ndinsert (a : α) (l : List α) : ndinsert a l = (insert a l : List α) :=
  rfl
#align multiset.coe_ndinsert Multiset.coe_ndinsert
-/

#print Multiset.ndinsert_zero /-
@[simp]
theorem ndinsert_zero (a : α) : ndinsert a 0 = {a} :=
  rfl
#align multiset.ndinsert_zero Multiset.ndinsert_zero
-/

#print Multiset.ndinsert_of_mem /-
@[simp]
theorem ndinsert_of_mem {a : α} {s : Multiset α} : a ∈ s → ndinsert a s = s :=
  Quot.inductionOn s fun l h => congr_arg coe <| insert_of_mem h
#align multiset.ndinsert_of_mem Multiset.ndinsert_of_mem
-/

#print Multiset.ndinsert_of_not_mem /-
@[simp]
theorem ndinsert_of_not_mem {a : α} {s : Multiset α} : a ∉ s → ndinsert a s = a ::ₘ s :=
  Quot.inductionOn s fun l h => congr_arg coe <| insert_of_not_mem h
#align multiset.ndinsert_of_not_mem Multiset.ndinsert_of_not_mem
-/

#print Multiset.mem_ndinsert /-
@[simp]
theorem mem_ndinsert {a b : α} {s : Multiset α} : a ∈ ndinsert b s ↔ a = b ∨ a ∈ s :=
  Quot.inductionOn s fun l => mem_insert_iff
#align multiset.mem_ndinsert Multiset.mem_ndinsert
-/

#print Multiset.le_ndinsert_self /-
@[simp]
theorem le_ndinsert_self (a : α) (s : Multiset α) : s ≤ ndinsert a s :=
  Quot.inductionOn s fun l => (sublist_insert _ _).Subperm
#align multiset.le_ndinsert_self Multiset.le_ndinsert_self
-/

#print Multiset.mem_ndinsert_self /-
@[simp]
theorem mem_ndinsert_self (a : α) (s : Multiset α) : a ∈ ndinsert a s :=
  mem_ndinsert.2 (Or.inl rfl)
#align multiset.mem_ndinsert_self Multiset.mem_ndinsert_self
-/

#print Multiset.mem_ndinsert_of_mem /-
theorem mem_ndinsert_of_mem {a b : α} {s : Multiset α} (h : a ∈ s) : a ∈ ndinsert b s :=
  mem_ndinsert.2 (Or.inr h)
#align multiset.mem_ndinsert_of_mem Multiset.mem_ndinsert_of_mem
-/

#print Multiset.length_ndinsert_of_mem /-
@[simp]
theorem length_ndinsert_of_mem {a : α} {s : Multiset α} (h : a ∈ s) :
    card (ndinsert a s) = card s := by simp [h]
#align multiset.length_ndinsert_of_mem Multiset.length_ndinsert_of_mem
-/

#print Multiset.length_ndinsert_of_not_mem /-
@[simp]
theorem length_ndinsert_of_not_mem {a : α} {s : Multiset α} (h : a ∉ s) :
    card (ndinsert a s) = card s + 1 := by simp [h]
#align multiset.length_ndinsert_of_not_mem Multiset.length_ndinsert_of_not_mem
-/

#print Multiset.dedup_cons /-
theorem dedup_cons {a : α} {s : Multiset α} : dedup (a ::ₘ s) = ndinsert a (dedup s) := by
  by_cases a ∈ s <;> simp [h]
#align multiset.dedup_cons Multiset.dedup_cons
-/

#print Multiset.Nodup.ndinsert /-
theorem Nodup.ndinsert (a : α) : Nodup s → Nodup (ndinsert a s) :=
  Quot.inductionOn s fun l => Nodup.insert
#align multiset.nodup.ndinsert Multiset.Nodup.ndinsert
-/

#print Multiset.ndinsert_le /-
theorem ndinsert_le {a : α} {s t : Multiset α} : ndinsert a s ≤ t ↔ s ≤ t ∧ a ∈ t :=
  ⟨fun h => ⟨le_trans (le_ndinsert_self _ _) h, mem_of_le h (mem_ndinsert_self _ _)⟩, fun ⟨l, m⟩ =>
    if h : a ∈ s then by simp [h, l]
    else by
      rw [ndinsert_of_not_mem h, ← cons_erase m, cons_le_cons_iff, ← le_cons_of_not_mem h,
          cons_erase m] <;>
        exact l⟩
#align multiset.ndinsert_le Multiset.ndinsert_le
-/

#print Multiset.attach_ndinsert /-
theorem attach_ndinsert (a : α) (s : Multiset α) :
    (s.ndinsert a).attach =
      ndinsert ⟨a, mem_ndinsert_self a s⟩ (s.attach.map fun p => ⟨p.1, mem_ndinsert_of_mem p.2⟩) :=
  have eq :
    ∀ h : ∀ p : { x // x ∈ s }, p.1 ∈ s,
      (fun p : { x // x ∈ s } => ⟨p.val, h p⟩ : { x // x ∈ s } → { x // x ∈ s }) = id :=
    fun h => funext fun p => Subtype.eq rfl
  have :
    ∀ (t) (eq : s.ndinsert a = t),
      t.attach =
        ndinsert ⟨a, Eq ▸ mem_ndinsert_self a s⟩
          (s.attach.map fun p => ⟨p.1, Eq ▸ mem_ndinsert_of_mem p.2⟩) :=
    by
    intro t ht
    by_cases a ∈ s
    · rw [ndinsert_of_mem h] at ht
      subst ht
      rw [Eq, map_id, ndinsert_of_mem (mem_attach _ _)]
    · rw [ndinsert_of_not_mem h] at ht
      subst ht
      simp [attach_cons, h]
  this _ rfl
#align multiset.attach_ndinsert Multiset.attach_ndinsert
-/

#print Multiset.disjoint_ndinsert_left /-
@[simp]
theorem disjoint_ndinsert_left {a : α} {s t : Multiset α} :
    Disjoint (ndinsert a s) t ↔ a ∉ t ∧ Disjoint s t :=
  Iff.trans (by simp [Disjoint]) disjoint_cons_left
#align multiset.disjoint_ndinsert_left Multiset.disjoint_ndinsert_left
-/

#print Multiset.disjoint_ndinsert_right /-
@[simp]
theorem disjoint_ndinsert_right {a : α} {s t : Multiset α} :
    Disjoint s (ndinsert a t) ↔ a ∉ s ∧ Disjoint s t := by
  rw [disjoint_comm, disjoint_ndinsert_left] <;> tauto
#align multiset.disjoint_ndinsert_right Multiset.disjoint_ndinsert_right
-/

/-! ### finset union -/


#print Multiset.ndunion /-
/-- `ndunion s t` is the lift of the list `union` operation. This operation
  does not respect multiplicities, unlike `s ∪ t`, but it is suitable as
  a union operation on `finset`. (`s ∪ t` would also work as a union operation
  on finset, but this is more efficient.) -/
def ndunion (s t : Multiset α) : Multiset α :=
  Quotient.liftOn₂ s t (fun l₁ l₂ => (l₁.union l₂ : Multiset α)) fun v₁ v₂ w₁ w₂ p₁ p₂ =>
    Quot.sound <| p₁.union p₂
#align multiset.ndunion Multiset.ndunion
-/

#print Multiset.coe_ndunion /-
@[simp]
theorem coe_ndunion (l₁ l₂ : List α) : @ndunion α _ l₁ l₂ = (l₁ ∪ l₂ : List α) :=
  rfl
#align multiset.coe_ndunion Multiset.coe_ndunion
-/

#print Multiset.zero_ndunion /-
@[simp]
theorem zero_ndunion (s : Multiset α) : ndunion 0 s = s :=
  Quot.inductionOn s fun l => rfl
#align multiset.zero_ndunion Multiset.zero_ndunion
-/

#print Multiset.cons_ndunion /-
@[simp]
theorem cons_ndunion (s t : Multiset α) (a : α) : ndunion (a ::ₘ s) t = ndinsert a (ndunion s t) :=
  Quotient.induction_on₂ s t fun l₁ l₂ => rfl
#align multiset.cons_ndunion Multiset.cons_ndunion
-/

#print Multiset.mem_ndunion /-
@[simp]
theorem mem_ndunion {s t : Multiset α} {a : α} : a ∈ ndunion s t ↔ a ∈ s ∨ a ∈ t :=
  Quotient.induction_on₂ s t fun l₁ l₂ => List.mem_union_iff
#align multiset.mem_ndunion Multiset.mem_ndunion
-/

#print Multiset.le_ndunion_right /-
theorem le_ndunion_right (s t : Multiset α) : t ≤ ndunion s t :=
  Quotient.induction_on₂ s t fun l₁ l₂ => (suffix_union_right _ _).Sublist.Subperm
#align multiset.le_ndunion_right Multiset.le_ndunion_right
-/

#print Multiset.subset_ndunion_right /-
theorem subset_ndunion_right (s t : Multiset α) : t ⊆ ndunion s t :=
  subset_of_le (le_ndunion_right s t)
#align multiset.subset_ndunion_right Multiset.subset_ndunion_right
-/

#print Multiset.ndunion_le_add /-
theorem ndunion_le_add (s t : Multiset α) : ndunion s t ≤ s + t :=
  Quotient.induction_on₂ s t fun l₁ l₂ => (union_sublist_append _ _).Subperm
#align multiset.ndunion_le_add Multiset.ndunion_le_add
-/

#print Multiset.ndunion_le /-
theorem ndunion_le {s t u : Multiset α} : ndunion s t ≤ u ↔ s ⊆ u ∧ t ≤ u :=
  Multiset.induction_on s (by simp)
    (by simp (config := { contextual := true }) [ndinsert_le, and_comm', and_left_comm])
#align multiset.ndunion_le Multiset.ndunion_le
-/

#print Multiset.subset_ndunion_left /-
theorem subset_ndunion_left (s t : Multiset α) : s ⊆ ndunion s t := fun a h =>
  mem_ndunion.2 <| Or.inl h
#align multiset.subset_ndunion_left Multiset.subset_ndunion_left
-/

#print Multiset.le_ndunion_left /-
theorem le_ndunion_left {s} (t : Multiset α) (d : Nodup s) : s ≤ ndunion s t :=
  (le_iff_subset d).2 <| subset_ndunion_left _ _
#align multiset.le_ndunion_left Multiset.le_ndunion_left
-/

#print Multiset.ndunion_le_union /-
theorem ndunion_le_union (s t : Multiset α) : ndunion s t ≤ s ∪ t :=
  ndunion_le.2 ⟨subset_of_le (le_union_left _ _), le_union_right _ _⟩
#align multiset.ndunion_le_union Multiset.ndunion_le_union
-/

#print Multiset.Nodup.ndunion /-
theorem Nodup.ndunion (s : Multiset α) {t : Multiset α} : Nodup t → Nodup (ndunion s t) :=
  Quotient.induction_on₂ s t fun l₁ l₂ => List.Nodup.union _
#align multiset.nodup.ndunion Multiset.Nodup.ndunion
-/

#print Multiset.ndunion_eq_union /-
@[simp]
theorem ndunion_eq_union {s t : Multiset α} (d : Nodup s) : ndunion s t = s ∪ t :=
  le_antisymm (ndunion_le_union _ _) <| union_le (le_ndunion_left _ d) (le_ndunion_right _ _)
#align multiset.ndunion_eq_union Multiset.ndunion_eq_union
-/

#print Multiset.dedup_add /-
theorem dedup_add (s t : Multiset α) : dedup (s + t) = ndunion s (dedup t) :=
  Quotient.induction_on₂ s t fun l₁ l₂ => congr_arg coe <| dedup_append _ _
#align multiset.dedup_add Multiset.dedup_add
-/

/-! ### finset inter -/


#print Multiset.ndinter /-
/-- `ndinter s t` is the lift of the list `∩` operation. This operation
  does not respect multiplicities, unlike `s ∩ t`, but it is suitable as
  an intersection operation on `finset`. (`s ∩ t` would also work as a union operation
  on finset, but this is more efficient.) -/
def ndinter (s t : Multiset α) : Multiset α :=
  filter (· ∈ t) s
#align multiset.ndinter Multiset.ndinter
-/

#print Multiset.coe_ndinter /-
@[simp]
theorem coe_ndinter (l₁ l₂ : List α) : @ndinter α _ l₁ l₂ = (l₁ ∩ l₂ : List α) :=
  rfl
#align multiset.coe_ndinter Multiset.coe_ndinter
-/

#print Multiset.zero_ndinter /-
@[simp]
theorem zero_ndinter (s : Multiset α) : ndinter 0 s = 0 :=
  rfl
#align multiset.zero_ndinter Multiset.zero_ndinter
-/

#print Multiset.cons_ndinter_of_mem /-
@[simp]
theorem cons_ndinter_of_mem {a : α} (s : Multiset α) {t : Multiset α} (h : a ∈ t) :
    ndinter (a ::ₘ s) t = a ::ₘ ndinter s t := by simp [ndinter, h]
#align multiset.cons_ndinter_of_mem Multiset.cons_ndinter_of_mem
-/

#print Multiset.ndinter_cons_of_not_mem /-
@[simp]
theorem ndinter_cons_of_not_mem {a : α} (s : Multiset α) {t : Multiset α} (h : a ∉ t) :
    ndinter (a ::ₘ s) t = ndinter s t := by simp [ndinter, h]
#align multiset.ndinter_cons_of_not_mem Multiset.ndinter_cons_of_not_mem
-/

#print Multiset.mem_ndinter /-
@[simp]
theorem mem_ndinter {s t : Multiset α} {a : α} : a ∈ ndinter s t ↔ a ∈ s ∧ a ∈ t :=
  mem_filter
#align multiset.mem_ndinter Multiset.mem_ndinter
-/

#print Multiset.Nodup.ndinter /-
@[simp]
theorem Nodup.ndinter {s : Multiset α} (t : Multiset α) : Nodup s → Nodup (ndinter s t) :=
  Nodup.filter _
#align multiset.nodup.ndinter Multiset.Nodup.ndinter
-/

#print Multiset.le_ndinter /-
theorem le_ndinter {s t u : Multiset α} : s ≤ ndinter t u ↔ s ≤ t ∧ s ⊆ u := by
  simp [ndinter, le_filter, subset_iff]
#align multiset.le_ndinter Multiset.le_ndinter
-/

#print Multiset.ndinter_le_left /-
theorem ndinter_le_left (s t : Multiset α) : ndinter s t ≤ s :=
  (le_ndinter.1 le_rfl).1
#align multiset.ndinter_le_left Multiset.ndinter_le_left
-/

#print Multiset.ndinter_subset_left /-
theorem ndinter_subset_left (s t : Multiset α) : ndinter s t ⊆ s :=
  subset_of_le (ndinter_le_left s t)
#align multiset.ndinter_subset_left Multiset.ndinter_subset_left
-/

#print Multiset.ndinter_subset_right /-
theorem ndinter_subset_right (s t : Multiset α) : ndinter s t ⊆ t :=
  (le_ndinter.1 le_rfl).2
#align multiset.ndinter_subset_right Multiset.ndinter_subset_right
-/

#print Multiset.ndinter_le_right /-
theorem ndinter_le_right {s} (t : Multiset α) (d : Nodup s) : ndinter s t ≤ t :=
  (le_iff_subset <| d.ndinter _).2 <| ndinter_subset_right _ _
#align multiset.ndinter_le_right Multiset.ndinter_le_right
-/

#print Multiset.inter_le_ndinter /-
theorem inter_le_ndinter (s t : Multiset α) : s ∩ t ≤ ndinter s t :=
  le_ndinter.2 ⟨inter_le_left _ _, subset_of_le <| inter_le_right _ _⟩
#align multiset.inter_le_ndinter Multiset.inter_le_ndinter
-/

#print Multiset.ndinter_eq_inter /-
@[simp]
theorem ndinter_eq_inter {s t : Multiset α} (d : Nodup s) : ndinter s t = s ∩ t :=
  le_antisymm (le_inter (ndinter_le_left _ _) (ndinter_le_right _ d)) (inter_le_ndinter _ _)
#align multiset.ndinter_eq_inter Multiset.ndinter_eq_inter
-/

#print Multiset.ndinter_eq_zero_iff_disjoint /-
theorem ndinter_eq_zero_iff_disjoint {s t : Multiset α} : ndinter s t = 0 ↔ Disjoint s t := by
  rw [← subset_zero] <;> simp [subset_iff, Disjoint]
#align multiset.ndinter_eq_zero_iff_disjoint Multiset.ndinter_eq_zero_iff_disjoint
-/

end Multiset

-- Assert that we define `finset` without the material on the set lattice.
-- Note that we cannot put this in `data.finset.basic` because we proved relevant lemmas there.
assert_not_exists Set.sInter

