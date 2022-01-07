import Mathbin.Order.LocallyFinite

/-!
# Intervals as finsets

This file provides basic results about all the `finset.Ixx`, which are defined in
`order.locally_finite`.

## TODO

This file was originally only about `finset.Ico a b` where `a b : ℕ`. No care has yet been taken to
generalize these lemmas properly and many lemmas about `Icc`, `Ioc`, `Ioo` are missing. In general,
what's to do is taking the lemmas in `data.x.intervals` and abstract away the concrete structure.
-/


variable {α : Type _}

namespace Finset

section Preorderₓ

variable [Preorderₓ α] [LocallyFiniteOrder α] {a b : α}

@[simp]
theorem nonempty_Icc : (Icc a b).Nonempty ↔ a ≤ b := by
  rw [← coe_nonempty, coe_Icc, Set.nonempty_Icc]

@[simp]
theorem nonempty_Ico : (Ico a b).Nonempty ↔ a < b := by
  rw [← coe_nonempty, coe_Ico, Set.nonempty_Ico]

@[simp]
theorem nonempty_Ioc : (Ioc a b).Nonempty ↔ a < b := by
  rw [← coe_nonempty, coe_Ioc, Set.nonempty_Ioc]

@[simp]
theorem nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔ a < b := by
  rw [← coe_nonempty, coe_Ioo, Set.nonempty_Ioo]

@[simp]
theorem Icc_eq_empty_iff : Icc a b = ∅ ↔ ¬a ≤ b := by
  rw [← coe_eq_empty, coe_Icc, Set.Icc_eq_empty_iff]

@[simp]
theorem Ico_eq_empty_iff : Ico a b = ∅ ↔ ¬a < b := by
  rw [← coe_eq_empty, coe_Ico, Set.Ico_eq_empty_iff]

@[simp]
theorem Ioc_eq_empty_iff : Ioc a b = ∅ ↔ ¬a < b := by
  rw [← coe_eq_empty, coe_Ioc, Set.Ioc_eq_empty_iff]

@[simp]
theorem Ioo_eq_empty_iff [DenselyOrdered α] : Ioo a b = ∅ ↔ ¬a < b := by
  rw [← coe_eq_empty, coe_Ioo, Set.Ioo_eq_empty_iff]

alias Icc_eq_empty_iff ↔ _ Finset.Icc_eq_empty

alias Ico_eq_empty_iff ↔ _ Finset.Ico_eq_empty

alias Ioc_eq_empty_iff ↔ _ Finset.Ioc_eq_empty

@[simp]
theorem Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅ :=
  eq_empty_iff_forall_not_mem.2 $ fun x hx => h ((mem_Ioo.1 hx).1.trans (mem_Ioo.1 hx).2)

@[simp]
theorem Icc_eq_empty_of_lt (h : b < a) : Icc a b = ∅ :=
  Icc_eq_empty h.not_le

@[simp]
theorem Ico_eq_empty_of_le (h : b ≤ a) : Ico a b = ∅ :=
  Ico_eq_empty h.not_lt

@[simp]
theorem Ioc_eq_empty_of_le (h : b ≤ a) : Ioc a b = ∅ :=
  Ioc_eq_empty h.not_lt

@[simp]
theorem Ioo_eq_empty_of_le (h : b ≤ a) : Ioo a b = ∅ :=
  Ioo_eq_empty h.not_lt

variable (a)

@[simp]
theorem Ico_self : Ico a a = ∅ := by
  rw [← coe_eq_empty, coe_Ico, Set.Ico_self]

@[simp]
theorem Ioc_self : Ioc a a = ∅ := by
  rw [← coe_eq_empty, coe_Ioc, Set.Ioc_self]

@[simp]
theorem Ioo_self : Ioo a a = ∅ := by
  rw [← coe_eq_empty, coe_Ioo, Set.Ioo_self]

variable {a b}

theorem left_mem_Icc : a ∈ Icc a b ↔ a ≤ b := by
  simp only [mem_Icc, true_andₓ, le_reflₓ]

theorem left_mem_Ico : a ∈ Ico a b ↔ a < b := by
  simp only [mem_Ico, true_andₓ, le_reflₓ]

theorem right_mem_Icc : b ∈ Icc a b ↔ a ≤ b := by
  simp only [mem_Icc, and_trueₓ, le_reflₓ]

theorem right_mem_Ioc : b ∈ Ioc a b ↔ a < b := by
  simp only [mem_Ioc, and_trueₓ, le_reflₓ]

@[simp]
theorem left_not_mem_Ioc : a ∉ Ioc a b := fun h => lt_irreflₓ _ (mem_Ioc.1 h).1

@[simp]
theorem left_not_mem_Ioo : a ∉ Ioo a b := fun h => lt_irreflₓ _ (mem_Ioo.1 h).1

@[simp]
theorem right_not_mem_Ico : b ∉ Ico a b := fun h => lt_irreflₓ _ (mem_Ico.1 h).2

@[simp]
theorem right_not_mem_Ioo : b ∉ Ioo a b := fun h => lt_irreflₓ _ (mem_Ioo.1 h).2

theorem Ico_filter_lt_of_le_left {a b c : α} [DecidablePred (· < c)] (hca : c ≤ a) :
    ((Ico a b).filter fun x => x < c) = ∅ :=
  Finset.filter_false_of_mem fun x hx => (hca.trans (mem_Ico.1 hx).1).not_lt

theorem Ico_filter_lt_of_right_le {a b c : α} [DecidablePred (· < c)] (hbc : b ≤ c) :
    ((Ico a b).filter fun x => x < c) = Ico a b :=
  Finset.filter_true_of_mem fun x hx => (mem_Ico.1 hx).2.trans_le hbc

theorem Ico_filter_lt_of_le_right {a b c : α} [DecidablePred (· < c)] (hcb : c ≤ b) :
    ((Ico a b).filter fun x => x < c) = Ico a c := by
  ext x
  rw [mem_filter, mem_Ico, mem_Ico, And.right_comm]
  exact and_iff_left_of_imp fun h => h.2.trans_le hcb

theorem Ico_filter_le_of_le_left {a b c : α} [DecidablePred ((· ≤ ·) c)] (hca : c ≤ a) :
    ((Ico a b).filter fun x => c ≤ x) = Ico a b :=
  Finset.filter_true_of_mem fun x hx => hca.trans (mem_Ico.1 hx).1

theorem Ico_filter_le_of_right_le {a b : α} [DecidablePred ((· ≤ ·) b)] : ((Ico a b).filter fun x => b ≤ x) = ∅ :=
  Finset.filter_false_of_mem fun x hx => (mem_Ico.1 hx).2.not_le

theorem Ico_filter_le_of_left_le {a b c : α} [DecidablePred ((· ≤ ·) c)] (hac : a ≤ c) :
    ((Ico a b).filter fun x => c ≤ x) = Ico c b := by
  ext x
  rw [mem_filter, mem_Ico, mem_Ico, and_comm, And.left_comm]
  exact and_iff_right_of_imp fun h => hac.trans h.1

/-- A set with upper and lower bounds in a locally finite order is a fintype -/
def _root_.set.fintype_of_mem_bounds {a b} {s : Set α} [DecidablePred (· ∈ s)] (ha : a ∈ LowerBounds s)
    (hb : b ∈ UpperBounds s) : Fintype s :=
  Set.fintypeSubset (Set.Icc a b) $ fun x hx => ⟨ha hx, hb hx⟩

theorem _root_.bdd_below.finite_of_bdd_above {s : Set α} (h₀ : BddBelow s) (h₁ : BddAbove s) : s.finite := by
  let ⟨a, ha⟩ := h₀
  let ⟨b, hb⟩ := h₁
  classical
  exact ⟨Set.fintypeOfMemBounds ha hb⟩

section Filter

variable (a b) [Fintype α]

theorem filter_lt_lt_eq_Ioo [DecidablePred fun j : α => a < j ∧ j < b] :
    (Finset.univ.filter fun j => a < j ∧ j < b) = Ioo a b := by
  ext
  simp

theorem filter_lt_le_eq_Ioc [DecidablePred fun j : α => a < j ∧ j ≤ b] :
    (Finset.univ.filter fun j => a < j ∧ j ≤ b) = Ioc a b := by
  ext
  simp

theorem filter_le_lt_eq_Ico [DecidablePred fun j : α => a ≤ j ∧ j < b] :
    (Finset.univ.filter fun j => a ≤ j ∧ j < b) = Ico a b := by
  ext
  simp

theorem filter_le_le_eq_Icc [DecidablePred fun j : α => a ≤ j ∧ j ≤ b] :
    (Finset.univ.filter fun j => a ≤ j ∧ j ≤ b) = Icc a b := by
  ext
  simp

theorem filter_lt_eq_Ioi [OrderTop α] [DecidablePred ((· < ·) a)] : (Finset.univ.filter fun j => a < j) = Ioi a := by
  ext
  simp

theorem filter_le_eq_Ici [OrderTop α] [DecidablePred ((· ≤ ·) a)] : (Finset.univ.filter fun j => a ≤ j) = Ici a := by
  ext
  simp

theorem filter_gt_eq_Iio [OrderBot α] [DecidablePred (· < a)] : (Finset.univ.filter fun j => j < a) = Iio a := by
  ext
  simp

theorem filter_ge_eq_Iic [OrderBot α] [DecidablePred (· ≤ a)] : (Finset.univ.filter fun j => j ≤ a) = Iic a := by
  ext
  simp

end Filter

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α] [LocallyFiniteOrder α] {a b c : α}

@[simp]
theorem Icc_self (a : α) : Icc a a = {a} := by
  rw [← coe_eq_singleton, coe_Icc, Set.Icc_self]

@[simp]
theorem Icc_eq_singleton_iff : Icc a b = {c} ↔ a = c ∧ b = c := by
  rw [← coe_eq_singleton, coe_Icc, Set.Icc_eq_singleton_iff]

section DecidableEq

variable [DecidableEq α]

theorem Icc_erase_left : (Icc a b).erase a = Ioc a b := by
  rw [← coe_inj, coe_erase, coe_Icc, coe_Ioc, Set.Icc_diff_left]

theorem Icc_erase_right : (Icc a b).erase b = Ico a b := by
  rw [← coe_inj, coe_erase, coe_Icc, coe_Ico, Set.Icc_diff_right]

theorem Ico_insert_right (h : a ≤ b) : insert b (Ico a b) = Icc a b := by
  rw [← coe_inj, coe_insert, coe_Icc, coe_Ico, Set.insert_eq, Set.union_comm, Set.Ico_union_right h]

theorem Ioo_insert_left (h : a < b) : insert a (Ioo a b) = Ico a b := by
  rw [← coe_inj, coe_insert, coe_Ioo, coe_Ico, Set.insert_eq, Set.union_comm, Set.Ioo_union_left h]

@[simp]
theorem Ico_inter_Ico_consecutive (a b c : α) : Ico a b ∩ Ico b c = ∅ := by
  refine' eq_empty_of_forall_not_mem fun x hx => _
  rw [mem_inter, mem_Ico, mem_Ico] at hx
  exact hx.1.2.not_le hx.2.1

theorem Ico_disjoint_Ico_consecutive (a b c : α) : Disjoint (Ico a b) (Ico b c) :=
  le_of_eqₓ $ Ico_inter_Ico_consecutive a b c

end DecidableEq

theorem Ico_filter_le_left {a b : α} [DecidablePred (· ≤ a)] (hab : a < b) : ((Ico a b).filter fun x => x ≤ a) = {a} :=
  by
  ext x
  rw [mem_filter, mem_Ico, mem_singleton, And.right_comm, ← le_antisymm_iffₓ, eq_comm]
  exact and_iff_left_of_imp fun h => h.le.trans_lt hab

theorem card_Ico_eq_card_Icc_sub_one (a b : α) : (Ico a b).card = (Icc a b).card - 1 := by
  classical
  by_cases' h : a ≤ b
  · rw [← Ico_insert_right h, card_insert_of_not_mem right_not_mem_Ico]
    exact (Nat.add_sub_cancel _ _).symm
    
  · rw [Ico_eq_empty fun h' => h h'.le, Icc_eq_empty h, card_empty, zero_tsub]
    

theorem card_Ioc_eq_card_Icc_sub_one (a b : α) : (Ioc a b).card = (Icc a b).card - 1 :=
  @card_Ico_eq_card_Icc_sub_one (OrderDual α) _ _ _ _

theorem card_Ioo_eq_card_Ico_sub_one (a b : α) : (Ioo a b).card = (Ico a b).card - 1 := by
  classical
  by_cases' h : a ≤ b
  · obtain rfl | h' := h.eq_or_lt
    · rw [Ioo_self, Ico_self, card_empty]
      
    rw [← Ioo_insert_left h', card_insert_of_not_mem left_not_mem_Ioo]
    exact (Nat.add_sub_cancel _ _).symm
    
  · rw [Ioo_eq_empty fun h' => h h'.le, Ico_eq_empty fun h' => h h'.le, card_empty, zero_tsub]
    

theorem card_Ioo_eq_card_Icc_sub_two (a b : α) : (Ioo a b).card = (Icc a b).card - 2 := by
  rw [card_Ioo_eq_card_Ico_sub_one, card_Ico_eq_card_Icc_sub_one]
  rfl

end PartialOrderₓ

section LinearOrderₓ

variable [LinearOrderₓ α] [LocallyFiniteOrder α] {a b : α}

theorem Ico_subset_Ico_iff {a₁ b₁ a₂ b₂ : α} (h : a₁ < b₁) : Ico a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ := by
  rw [← coe_subset, coe_Ico, coe_Ico, Set.Ico_subset_Ico_iff h]

theorem Ico_union_Ico_eq_Ico {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) : Ico a b ∪ Ico b c = Ico a c := by
  rw [← coe_inj, coe_union, coe_Ico, coe_Ico, coe_Ico, Set.Ico_union_Ico_eq_Ico hab hbc]

theorem Ico_union_Ico' {a b c d : α} (hcb : c ≤ b) (had : a ≤ d) : Ico a b ∪ Ico c d = Ico (min a c) (max b d) := by
  rw [← coe_inj, coe_union, coe_Ico, coe_Ico, coe_Ico, Set.Ico_union_Ico' hcb had]

theorem Ico_union_Ico {a b c d : α} (h₁ : min a b ≤ max c d) (h₂ : min c d ≤ max a b) :
    Ico a b ∪ Ico c d = Ico (min a c) (max b d) := by
  rw [← coe_inj, coe_union, coe_Ico, coe_Ico, coe_Ico, Set.Ico_union_Ico h₁ h₂]

theorem Ico_inter_Ico {a b c d : α} : Ico a b ∩ Ico c d = Ico (max a c) (min b d) := by
  rw [← coe_inj, coe_inter, coe_Ico, coe_Ico, coe_Ico, ← inf_eq_min, ← sup_eq_max, Set.Ico_inter_Ico]

@[simp]
theorem Ico_filter_lt (a b c : α) : ((Ico a b).filter fun x => x < c) = Ico a (min b c) := by
  cases le_totalₓ b c
  · rw [Ico_filter_lt_of_right_le h, min_eq_leftₓ h]
    
  · rw [Ico_filter_lt_of_le_right h, min_eq_rightₓ h]
    

@[simp]
theorem Ico_filter_le (a b c : α) : ((Ico a b).filter fun x => c ≤ x) = Ico (max a c) b := by
  cases le_totalₓ a c
  · rw [Ico_filter_le_of_left_le h, max_eq_rightₓ h]
    
  · rw [Ico_filter_le_of_le_left h, max_eq_leftₓ h]
    

@[simp]
theorem Ico_diff_Ico_left (a b c : α) : Ico a b \ Ico a c = Ico (max a c) b := by
  cases le_totalₓ a c
  · ext x
    rw [mem_sdiff, mem_Ico, mem_Ico, mem_Ico, max_eq_rightₓ h, And.right_comm, not_and, not_ltₓ]
    exact and_congr_left' ⟨fun hx => hx.2 hx.1, fun hx => ⟨h.trans hx, fun _ => hx⟩⟩
    
  · rw [Ico_eq_empty_of_le h, sdiff_empty, max_eq_leftₓ h]
    

@[simp]
theorem Ico_diff_Ico_right (a b c : α) : Ico a b \ Ico c b = Ico a (min b c) := by
  cases le_totalₓ b c
  · rw [Ico_eq_empty_of_le h, sdiff_empty, min_eq_leftₓ h]
    
  · ext x
    rw [mem_sdiff, mem_Ico, mem_Ico, mem_Ico, min_eq_rightₓ h, and_assoc, not_and', not_leₓ]
    exact and_congr_right' ⟨fun hx => hx.2 hx.1, fun hx => ⟨hx.trans_le h, fun _ => hx⟩⟩
    

end LinearOrderₓ

section OrderTop

variable [Preorderₓ α] [OrderTop α] [LocallyFiniteOrder α]

theorem _root_.bdd_below.finite {s : Set α} (hs : BddBelow s) : s.finite :=
  hs.finite_of_bdd_above $ OrderTop.bdd_above s

end OrderTop

section OrderBot

variable [Preorderₓ α] [OrderBot α] [LocallyFiniteOrder α]

theorem _root_.bdd_above.finite {s : Set α} (hs : BddAbove s) : s.finite :=
  hs.dual.finite

end OrderBot

section OrderedCancelAddCommMonoid

variable [OrderedCancelAddCommMonoid α] [HasExistsAddOfLe α] [DecidableEq α] [LocallyFiniteOrder α]

theorem image_add_left_Icc (a b c : α) : (Icc a b).Image ((· + ·) c) = Icc (c + a) (c + b) := by
  ext x
  rw [mem_image, mem_Icc]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_Icc] at hy
    exact ⟨add_le_add_left hy.1 c, add_le_add_left hy.2 c⟩
    
  · intro hx
    obtain ⟨y, hy⟩ := exists_add_of_le hx.1
    rw [add_assocₓ] at hy
    rw [hy] at hx
    exact ⟨a + y, mem_Icc.2 ⟨le_of_add_le_add_left hx.1, le_of_add_le_add_left hx.2⟩, hy.symm⟩
    

theorem image_add_left_Ico (a b c : α) : (Ico a b).Image ((· + ·) c) = Ico (c + a) (c + b) := by
  ext x
  rw [mem_image, mem_Ico]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_Ico] at hy
    exact ⟨add_le_add_left hy.1 c, add_lt_add_left hy.2 c⟩
    
  · intro hx
    obtain ⟨y, hy⟩ := exists_add_of_le hx.1
    rw [add_assocₓ] at hy
    rw [hy] at hx
    exact ⟨a + y, mem_Ico.2 ⟨le_of_add_le_add_left hx.1, lt_of_add_lt_add_left hx.2⟩, hy.symm⟩
    

theorem image_add_left_Ioc (a b c : α) : (Ioc a b).Image ((· + ·) c) = Ioc (c + a) (c + b) := by
  ext x
  rw [mem_image, mem_Ioc]
  refine' ⟨_, fun hx => _⟩
  · rintro ⟨y, hy, rfl⟩
    rw [mem_Ioc] at hy
    exact ⟨add_lt_add_left hy.1 c, add_le_add_left hy.2 c⟩
    
  · obtain ⟨y, hy⟩ := exists_add_of_le hx.1.le
    rw [add_assocₓ] at hy
    rw [hy] at hx
    exact ⟨a + y, mem_Ioc.2 ⟨lt_of_add_lt_add_left hx.1, le_of_add_le_add_left hx.2⟩, hy.symm⟩
    

theorem image_add_left_Ioo (a b c : α) : (Ioo a b).Image ((· + ·) c) = Ioo (c + a) (c + b) := by
  ext x
  rw [mem_image, mem_Ioo]
  refine' ⟨_, fun hx => _⟩
  · rintro ⟨y, hy, rfl⟩
    rw [mem_Ioo] at hy
    exact ⟨add_lt_add_left hy.1 c, add_lt_add_left hy.2 c⟩
    
  · obtain ⟨y, hy⟩ := exists_add_of_le hx.1.le
    rw [add_assocₓ] at hy
    rw [hy] at hx
    exact ⟨a + y, mem_Ioo.2 ⟨lt_of_add_lt_add_left hx.1, lt_of_add_lt_add_left hx.2⟩, hy.symm⟩
    

theorem image_add_right_Icc (a b c : α) : ((Icc a b).Image fun x => x + c) = Icc (a + c) (b + c) := by
  simp_rw [add_commₓ _ c]
  exact image_add_left_Icc a b c

theorem image_add_right_Ico (a b c : α) : ((Ico a b).Image fun x => x + c) = Ico (a + c) (b + c) := by
  simp_rw [add_commₓ _ c]
  exact image_add_left_Ico a b c

theorem image_add_right_Ioc (a b c : α) : ((Ioc a b).Image fun x => x + c) = Ioc (a + c) (b + c) := by
  simp_rw [add_commₓ _ c]
  exact image_add_left_Ioc a b c

theorem image_add_right_Ioo (a b c : α) : ((Ioo a b).Image fun x => x + c) = Ioo (a + c) (b + c) := by
  simp_rw [add_commₓ _ c]
  exact image_add_left_Ioo a b c

end OrderedCancelAddCommMonoid

end Finset

