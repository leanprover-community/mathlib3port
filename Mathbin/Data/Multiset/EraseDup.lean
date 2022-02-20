/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Multiset.Nodup

/-!
# Erasing duplicates in a multiset.
-/


namespace Multiset

open List

variable {α β : Type _} [DecidableEq α]

/-! ### erase_dup -/


/-- `erase_dup s` removes duplicates from `s`, yielding a `nodup` multiset. -/
def eraseDup (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => (l.eraseDup : Multiset α)) fun s t p => Quot.sound p.eraseDup

@[simp]
theorem coe_erase_dup (l : List α) : @eraseDup α _ l = l.eraseDup :=
  rfl

@[simp]
theorem erase_dup_zero : @eraseDup α _ 0 = 0 :=
  rfl

@[simp]
theorem mem_erase_dup {a : α} {s : Multiset α} : a ∈ eraseDup s ↔ a ∈ s :=
  (Quot.induction_on s) fun l => mem_erase_dup

@[simp]
theorem erase_dup_cons_of_mem {a : α} {s : Multiset α} : a ∈ s → eraseDup (a ::ₘ s) = eraseDup s :=
  (Quot.induction_on s) fun l m => @congr_argₓ _ _ _ _ coe <| erase_dup_cons_of_mem m

@[simp]
theorem erase_dup_cons_of_not_mem {a : α} {s : Multiset α} : a ∉ s → eraseDup (a ::ₘ s) = a ::ₘ eraseDup s :=
  (Quot.induction_on s) fun l m => congr_argₓ coe <| erase_dup_cons_of_not_mem m

theorem erase_dup_le (s : Multiset α) : eraseDup s ≤ s :=
  (Quot.induction_on s) fun l => (erase_dup_sublist _).Subperm

theorem erase_dup_subset (s : Multiset α) : eraseDup s ⊆ s :=
  subset_of_le <| erase_dup_le _

theorem subset_erase_dup (s : Multiset α) : s ⊆ eraseDup s := fun a => mem_erase_dup.2

@[simp]
theorem erase_dup_subset' {s t : Multiset α} : eraseDup s ⊆ t ↔ s ⊆ t :=
  ⟨Subset.trans (subset_erase_dup _), Subset.trans (erase_dup_subset _)⟩

@[simp]
theorem subset_erase_dup' {s t : Multiset α} : s ⊆ eraseDup t ↔ s ⊆ t :=
  ⟨fun h => Subset.trans h (erase_dup_subset _), fun h => Subset.trans h (subset_erase_dup _)⟩

@[simp]
theorem nodup_erase_dup (s : Multiset α) : Nodup (eraseDup s) :=
  Quot.induction_on s nodup_erase_dup

theorem erase_dup_eq_self {s : Multiset α} : eraseDup s = s ↔ Nodup s :=
  ⟨fun e => e ▸ nodup_erase_dup s, (Quot.induction_on s) fun l h => congr_argₓ coe h.eraseDup⟩

alias erase_dup_eq_self ↔ _ Multiset.Nodup.erase_dup

alias erase_dup_eq_self ↔ _ Multiset.Nodup.erase_dup

theorem erase_dup_eq_zero {s : Multiset α} : eraseDup s = 0 ↔ s = 0 :=
  ⟨fun h => eq_zero_of_subset_zero <| h ▸ subset_erase_dup _, fun h => h.symm ▸ erase_dup_zero⟩

@[simp]
theorem erase_dup_singleton {a : α} : eraseDup ({a} : Multiset α) = {a} :=
  (nodup_singleton _).eraseDup

theorem le_erase_dup {s t : Multiset α} : s ≤ eraseDup t ↔ s ≤ t ∧ Nodup s :=
  ⟨fun h => ⟨le_transₓ h (erase_dup_le _), nodup_of_le h (nodup_erase_dup _)⟩, fun ⟨l, d⟩ =>
    (le_iff_subset d).2 <| Subset.trans (subset_of_le l) (subset_erase_dup _)⟩

theorem erase_dup_ext {s t : Multiset α} : eraseDup s = eraseDup t ↔ ∀ a, a ∈ s ↔ a ∈ t := by
  simp [nodup_ext]

theorem erase_dup_map_erase_dup_eq [DecidableEq β] (f : α → β) (s : Multiset α) :
    eraseDup (map f (eraseDup s)) = eraseDup (map f s) := by
  simp [erase_dup_ext]

@[simp]
theorem erase_dup_nsmul {s : Multiset α} {n : ℕ} (h0 : n ≠ 0) : (n • s).eraseDup = s.eraseDup := by
  ext a
  by_cases' h : a ∈ s <;> simp [h, h0]

theorem Nodup.le_erase_dup_iff_le {s t : Multiset α} (hno : s.Nodup) : s ≤ t.eraseDup ↔ s ≤ t := by
  simp [le_erase_dup, hno]

end Multiset

theorem Multiset.Nodup.le_nsmul_iff_le {α : Type _} {s t : Multiset α} {n : ℕ} (h : s.Nodup) (hn : n ≠ 0) :
    s ≤ n • t ↔ s ≤ t := by
  classical
  rw [← h.le_erase_dup_iff_le, Iff.comm, ← h.le_erase_dup_iff_le]
  simp [hn]

