import Mathbin.Data.Set.Intervals.OrdConnected

/-!
# The covering relation

This file defines the covering relation in an order. `b` is said to cover `a` if `a < b` and there
is no element in between. ∃ b, a < b

## Notation

`a ⋖ b` means that `b` covers `a`.
-/


open Set

variable {α β : Type _}

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

alias not_covers_iff ↔ exists_lt_lt_of_not_covers _

alias exists_lt_lt_of_not_covers ← LT.lt.exists_lt_lt

/-- In a dense order, nothing covers anything. -/
theorem not_covers [DenselyOrdered α] : ¬a ⋖ b := fun h =>
  let ⟨c, hc⟩ := exists_between h.1
  h.2 hc.1 hc.2

theorem densely_ordered_iff_forall_not_covers : DenselyOrdered α ↔ ∀ a b : α, ¬a ⋖ b :=
  ⟨fun h a b => @not_covers _ _ _ _ h, fun h => ⟨fun a b hab => exists_lt_lt_of_not_covers hab $ h _ _⟩⟩

open OrderDual

@[simp]
theorem to_dual_covers_to_dual_iff : to_dual b ⋖ to_dual a ↔ a ⋖ b :=
  and_congr_right' $ forall_congrₓ $ fun c => forall_swap

@[simp]
theorem of_dual_covers_of_dual_iff {a b : OrderDual α} : of_dual a ⋖ of_dual b ↔ b ⋖ a :=
  and_congr_right' $ forall_congrₓ $ fun c => forall_swap

alias to_dual_covers_to_dual_iff ↔ _ Covers.to_dual

alias of_dual_covers_of_dual_iff ↔ _ Covers.of_dual

end LT

section Preorderₓ

variable [Preorderₓ α] [Preorderₓ β] {a b : α} {f : α ↪o β} {e : α ≃o β}

theorem Covers.le (h : a ⋖ b) : a ≤ b :=
  h.1.le

protected theorem Covers.ne (h : a ⋖ b) : a ≠ b :=
  h.lt.ne

theorem Covers.ne' (h : a ⋖ b) : b ≠ a :=
  h.lt.ne'

instance Covers.is_irrefl : IsIrrefl α (· ⋖ ·) :=
  ⟨fun a ha => ha.ne rfl⟩

theorem Covers.Ioo_eq (h : a ⋖ b) : Ioo a b = ∅ :=
  eq_empty_iff_forall_not_mem.2 $ fun x hx => h.2 hx.1 hx.2

theorem Covers.of_image (h : f a ⋖ f b) : a ⋖ b := by
  refine' ⟨_, fun c hac hcb => _⟩
  · rw [← OrderEmbedding.lt_iff_lt f]
    exact h.1
    
  rw [← OrderEmbedding.lt_iff_lt f] at hac hcb
  exact h.2 hac hcb

theorem Covers.image (hab : a ⋖ b) (h : (Set.Range f).OrdConnected) : f a ⋖ f b := by
  refine' ⟨f.strict_mono hab.1, fun c ha hb => _⟩
  obtain ⟨c, rfl⟩ := h.out (mem_range_self _) (mem_range_self _) ⟨ha.le, hb.le⟩
  rw [f.lt_iff_lt] at ha hb
  exact hab.2 ha hb

protected theorem Set.OrdConnected.image_covers_image_iff (h : (Set.Range f).OrdConnected) : f a ⋖ f b ↔ a ⋖ b :=
  ⟨Covers.of_image, fun hab => hab.image h⟩

@[simp]
theorem apply_covers_apply_iff : e a ⋖ e b ↔ a ⋖ b :=
  ⟨Covers.of_image, fun hab => by
    refine' ⟨e.strict_mono hab.1, fun c ha hb => _⟩
    rw [← e.symm.lt_iff_lt, OrderIso.symm_apply_apply] at ha hb
    exact hab.2 ha hb⟩

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

