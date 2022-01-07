import Mathbin.Data.Set.Intervals.Basic

/-!
# The covering relation

This file defines the covering relation in an order. `b` is said to cover `a` if `a < b` and there
is no element in between. ∃ b, a < b

## Notation

`a ⋖ b` means that `b` covers `a`.
-/


open Set

variable {α : Type _}

section LT

variable [LT α] {a b : α}

/-- `covers a b` means that `b` covers `a`: `a < b` and there is no element in between. -/
def Covers (a b : α) : Prop :=
  a < b ∧ ∀ ⦃c⦄, a < c → ¬c < b

infixl:50 " ⋖ " => Covers

theorem Covers.lt (h : a ⋖ b) : a < b :=
  h.1

/-- If `a < b`, then `b` does not cover `a` iff there's an element in between. -/
theorem not_covers_iff (h : a < b) : ¬a ⋖ b ↔ ∃ c, a < c ∧ c < b := by
  simp_rw [Covers, not_and, not_forall, exists_prop, not_not]
  exact imp_iff_right h

open OrderDual

@[simp]
theorem to_dual_covers_to_dual_iff : to_dual b ⋖ to_dual a ↔ a ⋖ b :=
  and_congr_right' $ forall_congrₓ $ fun c => forall_swap

alias to_dual_covers_to_dual_iff ↔ _ Covers.to_dual

/-- In a dense order, nothing covers anything. -/
theorem not_covers [DenselyOrdered α] : ¬a ⋖ b := fun h =>
  let ⟨c, hc⟩ := exists_between h.1
  h.2 hc.1 hc.2

end LT

section Preorderₓ

variable [Preorderₓ α] {a b : α}

theorem Covers.le (h : a ⋖ b) : a ≤ b :=
  h.1.le

protected theorem Covers.ne (h : a ⋖ b) : a ≠ b :=
  h.lt.ne

theorem Covers.ne' (h : a ⋖ b) : b ≠ a :=
  h.lt.ne'

theorem Covers.Ioo_eq (h : a ⋖ b) : Ioo a b = ∅ :=
  eq_empty_iff_forall_not_mem.2 $ fun x hx => h.2 hx.1 hx.2

instance Covers.is_irrefl : IsIrrefl α (· ⋖ ·) :=
  ⟨fun a ha => ha.ne rfl⟩

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α] {a b : α}

theorem Covers.Ico_eq (h : a ⋖ b) : Ico a b = {a} := by
  rw [← Set.Ioo_union_left h.lt, h.Ioo_eq, empty_union]

theorem Covers.Ioc_eq (h : a ⋖ b) : Ioc a b = {b} := by
  rw [← Set.Ioo_union_right h.lt, h.Ioo_eq, empty_union]

theorem Covers.Icc_eq (h : a ⋖ b) : Icc a b = {a, b} := by
  rw [← Set.Ico_union_right h.le, h.Ico_eq]
  rfl

end PartialOrderₓ

