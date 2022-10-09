/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathbin.Order.SuccPred.Basic

/-!
# Successor and predecessor limits

We define the predicate `order.is_succ_limit` for "successor limits", values that don't cover any
others. They are so named since they can't be the successors of anything smaller. We define
`order.is_pred_limit` analogously, and prove basic results.

## Todo

The plan is to eventually replace `ordinal.is_limit` and `cardinal.is_limit` with the common
predicate `order.is_succ_limit`.
-/


variable {α : Type _}

namespace Order

open Function Set OrderDual

/-! ### Successor limits -/


section LT

variable [LT α]

/-- A successor limit is a value that doesn't cover any other.

It's so named because in a successor order, a successor limit can't be the successor of anything
smaller. -/
def IsSuccLimit (a : α) : Prop :=
  ∀ b, ¬b ⋖ a

theorem not_is_succ_limit_iff_exists_covby (a : α) : ¬IsSuccLimit a ↔ ∃ b, b ⋖ a := by simp [is_succ_limit]

@[simp]
theorem is_succ_limit_of_dense [DenselyOrdered α] (a : α) : IsSuccLimit a := fun b => not_covby

end LT

section Preorderₓ

variable [Preorderₓ α] {a : α}

protected theorem _root_.is_min.is_succ_limit : IsMin a → IsSuccLimit a := fun h b hab => not_is_min_of_lt hab.lt h

theorem is_succ_limit_bot [OrderBot α] : IsSuccLimit (⊥ : α) :=
  is_min_bot.IsSuccLimit

variable [SuccOrder α]

protected theorem IsSuccLimit.is_max (h : IsSuccLimit (succ a)) : IsMax a := by
  by_contra H
  exact h a (covby_succ_of_not_is_max H)

theorem not_is_succ_limit_succ_of_not_is_max (ha : ¬IsMax a) : ¬IsSuccLimit (succ a) := by
  contrapose! ha
  exact ha.is_max

section NoMaxOrder

variable [NoMaxOrder α]

theorem IsSuccLimit.succ_ne (h : IsSuccLimit a) (b : α) : succ b ≠ a := by
  rintro rfl
  exact not_is_max _ h.is_max

@[simp]
theorem not_is_succ_limit_succ (a : α) : ¬IsSuccLimit (succ a) := fun h => h.succ_ne _ rfl

end NoMaxOrder

section IsSuccArchimedean

variable [IsSuccArchimedean α]

theorem IsSuccLimit.is_min_of_no_max [NoMaxOrder α] (h : IsSuccLimit a) : IsMin a := fun b hb => by
  rcases hb.exists_succ_iterate with ⟨_ | n, rfl⟩
  · exact le_rflₓ
    
  · rw [iterate_succ_apply'] at h
    exact (not_is_succ_limit_succ _ h).elim
    

@[simp]
theorem is_succ_limit_iff_of_no_max [NoMaxOrder α] : IsSuccLimit a ↔ IsMin a :=
  ⟨IsSuccLimit.is_min_of_no_max, IsMin.is_succ_limit⟩

theorem not_is_succ_limit_of_no_max [NoMinOrder α] [NoMaxOrder α] : ¬IsSuccLimit a := by simp

end IsSuccArchimedean

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α] [SuccOrder α] {a b : α} {C : α → Sort _}

theorem is_succ_limit_of_succ_ne (h : ∀ b, succ b ≠ a) : IsSuccLimit a := fun b hba => h b hba.succ_eq

theorem not_is_succ_limit_iff : ¬IsSuccLimit a ↔ ∃ b, ¬IsMax b ∧ succ b = a := by
  rw [not_is_succ_limit_iff_exists_covby]
  refine' exists_congr fun b => ⟨fun hba => ⟨hba.lt.not_is_max, hba.succ_eq⟩, _⟩
  rintro ⟨h, rfl⟩
  exact covby_succ_of_not_is_max h

/-- See `not_is_succ_limit_iff` for a version that states that `a` is a successor of a value other
than itself. -/
theorem mem_range_succ_of_not_is_succ_limit (h : ¬IsSuccLimit a) : a ∈ Range (@succ α _ _) := by
  cases' not_is_succ_limit_iff.1 h with b hb
  exact ⟨b, hb.2⟩

theorem is_succ_limit_of_succ_lt (H : ∀ a < b, succ a < b) : IsSuccLimit b := fun a hab => (H a hab.lt).Ne hab.succ_eq

theorem IsSuccLimit.succ_lt (hb : IsSuccLimit b) (ha : a < b) : succ a < b := by
  by_cases h:IsMax a
  · rwa [h.succ_eq]
    
  · rw [lt_iff_le_and_neₓ, succ_le_iff_of_not_is_max h]
    refine' ⟨ha, fun hab => _⟩
    subst hab
    exact (h hb.is_max).elim
    

theorem IsSuccLimit.succ_lt_iff (hb : IsSuccLimit b) : succ a < b ↔ a < b :=
  ⟨fun h => (le_succ a).trans_lt h, hb.succ_lt⟩

theorem is_succ_limit_iff_succ_lt : IsSuccLimit b ↔ ∀ a < b, succ a < b :=
  ⟨fun hb a => hb.succ_lt, is_succ_limit_of_succ_lt⟩

/-- A value can be built by building it on successors and successor limits. -/
@[elabAsElim]
noncomputable def isSuccLimitRecOn (b : α) (hs : ∀ a, ¬IsMax a → C (succ a)) (hl : ∀ a, IsSuccLimit a → C a) : C b := by
  by_cases hb:is_succ_limit b
  · exact hl b hb
    
  · have H := Classical.choose_spec (not_is_succ_limit_iff.1 hb)
    rw [← H.2]
    exact hs _ H.1
    

theorem is_succ_limit_rec_on_limit (hs : ∀ a, ¬IsMax a → C (succ a)) (hl : ∀ a, IsSuccLimit a → C a)
    (hb : IsSuccLimit b) : @isSuccLimitRecOn α _ _ C b hs hl = hl b hb := by
  classical
  exact dif_pos hb

theorem is_succ_limit_rec_on_succ' (hs : ∀ a, ¬IsMax a → C (succ a)) (hl : ∀ a, IsSuccLimit a → C a) {b : α}
    (hb : ¬IsMax b) : @isSuccLimitRecOn α _ _ C (succ b) hs hl = hs b hb := by
  have hb' := not_is_succ_limit_succ_of_not_is_max hb
  have H := Classical.choose_spec (not_is_succ_limit_iff.1 hb')
  rw [is_succ_limit_rec_on]
  simp only [cast_eq_iff_heq, hb', not_false_iff, eq_mpr_eq_cast, dif_neg]
  congr
  · exact (succ_eq_succ_iff_of_not_is_max H.1 hb).1 H.2
    
  · apply proof_irrel_heq
    

section NoMaxOrder

variable [NoMaxOrder α]

@[simp]
theorem is_succ_limit_rec_on_succ (hs : ∀ a, ¬IsMax a → C (succ a)) (hl : ∀ a, IsSuccLimit a → C a) (b : α) :
    @isSuccLimitRecOn α _ _ C (succ b) hs hl = hs b (not_is_max b) :=
  is_succ_limit_rec_on_succ' _ _ _

theorem is_succ_limit_iff_succ_ne : IsSuccLimit a ↔ ∀ b, succ b ≠ a :=
  ⟨IsSuccLimit.succ_ne, is_succ_limit_of_succ_ne⟩

theorem not_is_succ_limit_iff' : ¬IsSuccLimit a ↔ a ∈ Range (@succ α _ _) := by
  simp_rw [is_succ_limit_iff_succ_ne, not_forall, not_ne_iff]
  rfl

end NoMaxOrder

section IsSuccArchimedean

variable [IsSuccArchimedean α]

protected theorem IsSuccLimit.is_min (h : IsSuccLimit a) : IsMin a := fun b hb => by
  revert h
  refine' Succ.rec (fun _ => le_rflₓ) (fun c hbc H hc => _) hb
  have := hc.is_max.succ_eq
  rw [this] at hc⊢
  exact H hc

@[simp]
theorem is_succ_limit_iff : IsSuccLimit a ↔ IsMin a :=
  ⟨IsSuccLimit.is_min, IsMin.is_succ_limit⟩

theorem not_is_succ_limit [NoMinOrder α] : ¬IsSuccLimit a := by simp

end IsSuccArchimedean

end PartialOrderₓ

/-! ### Predecessor limits -/


section LT

variable [LT α] {a : α}

/-- A predecessor limit is a value that isn't covered by any other.

It's so named because in a predecessor order, a predecessor limit can't be the predecessor of
anything greater. -/
def IsPredLimit (a : α) : Prop :=
  ∀ b, ¬a ⋖ b

theorem not_is_pred_limit_iff_exists_covby (a : α) : ¬IsPredLimit a ↔ ∃ b, a ⋖ b := by simp [is_pred_limit]

theorem is_pred_limit_of_dense [DenselyOrdered α] (a : α) : IsPredLimit a := fun b => not_covby

@[simp]
theorem is_succ_limit_to_dual_iff : IsSuccLimit (toDual a) ↔ IsPredLimit a := by simp [is_succ_limit, is_pred_limit]

@[simp]
theorem is_pred_limit_to_dual_iff : IsPredLimit (toDual a) ↔ IsSuccLimit a := by simp [is_succ_limit, is_pred_limit]

alias is_succ_limit_to_dual_iff ↔ _ is_pred_limit.dual

alias is_pred_limit_to_dual_iff ↔ _ is_succ_limit.dual

end LT

section Preorderₓ

variable [Preorderₓ α] {a : α}

protected theorem _root_.is_max.is_pred_limit : IsMax a → IsPredLimit a := fun h b hab => not_is_max_of_lt hab.lt h

theorem is_pred_limit_top [OrderTop α] : IsPredLimit (⊤ : α) :=
  is_max_top.IsPredLimit

variable [PredOrder α]

protected theorem IsPredLimit.is_min (h : IsPredLimit (pred a)) : IsMin a := by
  by_contra H
  exact h a (pred_covby_of_not_is_min H)

theorem not_is_pred_limit_pred_of_not_is_min (ha : ¬IsMin a) : ¬IsPredLimit (pred a) := by
  contrapose! ha
  exact ha.is_min

section NoMinOrder

variable [NoMinOrder α]

theorem IsPredLimit.pred_ne (h : IsPredLimit a) (b : α) : pred b ≠ a := by
  rintro rfl
  exact not_is_min _ h.is_min

@[simp]
theorem not_is_pred_limit_pred (a : α) : ¬IsPredLimit (pred a) := fun h => h.pred_ne _ rfl

end NoMinOrder

section IsPredArchimedean

variable [IsPredArchimedean α]

protected theorem IsPredLimit.is_max_of_no_min [NoMinOrder α] (h : IsPredLimit a) : IsMax a :=
  h.dual.is_min_of_no_max

@[simp]
theorem is_pred_limit_iff_of_no_min [NoMinOrder α] : IsPredLimit a ↔ IsMax a :=
  is_succ_limit_to_dual_iff.symm.trans is_succ_limit_iff_of_no_max

theorem not_is_pred_limit_of_no_min [NoMinOrder α] [NoMaxOrder α] : ¬IsPredLimit a := by simp

end IsPredArchimedean

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α] [PredOrder α] {a b : α} {C : α → Sort _}

theorem is_pred_limit_of_pred_ne (h : ∀ b, pred b ≠ a) : IsPredLimit a := fun b hba => h b hba.pred_eq

theorem not_is_pred_limit_iff : ¬IsPredLimit a ↔ ∃ b, ¬IsMin b ∧ pred b = a := by
  rw [← is_succ_limit_to_dual_iff]
  exact not_is_succ_limit_iff

/-- See `not_is_pred_limit_iff` for a version that states that `a` is a successor of a value other
than itself. -/
theorem mem_range_pred_of_not_is_pred_limit (h : ¬IsPredLimit a) : a ∈ Range (@pred α _ _) := by
  cases' not_is_pred_limit_iff.1 h with b hb
  exact ⟨b, hb.2⟩

theorem is_pred_limit_of_pred_lt (H : ∀ a > b, pred a < b) : IsPredLimit b := fun a hab => (H a hab.lt).Ne hab.pred_eq

theorem IsPredLimit.lt_pred (h : IsPredLimit a) : a < b → a < pred b :=
  h.dual.succ_lt

theorem IsPredLimit.lt_pred_iff (h : IsPredLimit a) : a < pred b ↔ a < b :=
  h.dual.succ_lt_iff

theorem is_pred_limit_iff_lt_pred : IsPredLimit a ↔ ∀ ⦃b⦄, a < b → a < pred b :=
  is_succ_limit_to_dual_iff.symm.trans is_succ_limit_iff_succ_lt

/-- A value can be built by building it on predecessors and predecessor limits. -/
@[elabAsElim]
noncomputable def isPredLimitRecOn (b : α) (hs : ∀ a, ¬IsMin a → C (pred a)) (hl : ∀ a, IsPredLimit a → C a) : C b :=
  @isSuccLimitRecOn αᵒᵈ _ _ _ _ hs fun a ha => hl _ ha.dual

theorem is_pred_limit_rec_on_limit (hs : ∀ a, ¬IsMin a → C (pred a)) (hl : ∀ a, IsPredLimit a → C a)
    (hb : IsPredLimit b) : @isPredLimitRecOn α _ _ C b hs hl = hl b hb :=
  is_succ_limit_rec_on_limit _ _ hb.dual

theorem is_pred_limit_rec_on_pred' (hs : ∀ a, ¬IsMin a → C (pred a)) (hl : ∀ a, IsPredLimit a → C a) {b : α}
    (hb : ¬IsMin b) : @isPredLimitRecOn α _ _ C (pred b) hs hl = hs b hb :=
  is_succ_limit_rec_on_succ' _ _ _

section NoMinOrder

variable [NoMinOrder α]

@[simp]
theorem is_pred_limit_rec_on_pred (hs : ∀ a, ¬IsMin a → C (pred a)) (hl : ∀ a, IsPredLimit a → C a) (b : α) :
    @isPredLimitRecOn α _ _ C (pred b) hs hl = hs b (not_is_min b) :=
  is_succ_limit_rec_on_succ _ _ _

end NoMinOrder

section IsPredArchimedean

variable [IsPredArchimedean α]

protected theorem IsPredLimit.is_max (h : IsPredLimit a) : IsMax a :=
  h.dual.IsMin

@[simp]
theorem is_pred_limit_iff : IsPredLimit a ↔ IsMax a :=
  is_succ_limit_to_dual_iff.symm.trans is_succ_limit_iff

theorem not_is_pred_limit [NoMaxOrder α] : ¬IsPredLimit a := by simp

end IsPredArchimedean

end PartialOrderₓ

end Order

