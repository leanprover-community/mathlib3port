/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathbin.Order.SuccPred.Basic

/-!
# Successor and predecessor limits

We define the predicate `order.is_succ_limit` for "successor limits", values that aren't successors,
except possibly of themselves. We define `order.is_pred_limit` analogously, and prove basic results.

## Todo

The plan is to eventually replace `ordinal.is_limit` and `cardinal.is_limit` with the common
predicate `order.is_succ_limit`.
-/


variable {α : Type _} {a b : α}

open Function Set

/-! ### Successor limits -/


namespace Order

section Preorderₓ

variable [Preorderₓ α] [SuccOrder α]

/-- A successor limit is a value that isn't a successor, except possibly of itself. -/
def IsSuccLimit (a : α) : Prop :=
  ∀ b, succ b = a → IsMax b

protected theorem IsSuccLimit.is_max (h : IsSuccLimit (succ a)) : IsMax a :=
  h a rfl

theorem not_is_succ_limit_succ_of_not_is_max (ha : ¬IsMax a) : ¬IsSuccLimit (succ a) := fun h => ha (h a rfl)

protected theorem _root_.is_min.is_succ_limit (h : IsMin a) : IsSuccLimit a := by
  rintro b rfl
  exact max_of_succ_le (h <| le_succ b)

theorem is_succ_limit_of_succ_ne (h : ∀ b, succ b ≠ a) : IsSuccLimit a := fun b hb => (h _ hb).elim

theorem not_is_succ_limit_iff : ¬IsSuccLimit a ↔ ∃ b, ¬IsMax b ∧ succ b = a := by
  simp [is_succ_limit, and_comm]

/-- See `order.not_is_succ_limit_iff` for a version that states that `a` is a successor of a value
other than itself. -/
theorem mem_range_succ_of_not_is_succ_limit (h : ¬IsSuccLimit a) : a ∈ Range (@succ α _ _) := by
  cases' not_is_succ_limit_iff.1 h with b hb
  exact ⟨b, hb.2⟩

theorem is_succ_limit_of_succ_lt (H : ∀ a < b, succ a < b) : IsSuccLimit b := by
  rintro a rfl
  by_contra ha
  exact (H a <| lt_succ_of_not_is_max ha).False

/-- A value can be built by building it on successors and successor limits.

Note that you need a partial order for data built using this to behave nicely on successors. -/
@[elabAsElim]
noncomputable def isSuccLimitRecOn {C : α → Sort _} (b) (hs : ∀ a, ¬IsMax a → C (succ a))
    (hl : ∀ a, IsSuccLimit a → C a) : C b := by
  by_cases' hb : is_succ_limit b
  · exact hl b hb
    
  · have H := Classical.some_spec (not_is_succ_limit_iff.1 hb)
    rw [← H.2]
    exact hs _ H.1
    

theorem is_succ_limit_rec_on_limit {C : α → Sort _} (hs : ∀ a, ¬IsMax a → C (succ a)) (hl : ∀ a, IsSuccLimit a → C a)
    (hb : IsSuccLimit b) : @isSuccLimitRecOn α _ _ C b hs hl = hl b hb := by
  classical
  exact dif_pos hb

section NoMaxOrder

variable [NoMaxOrder α]

theorem IsSuccLimit.succ_ne (h : IsSuccLimit a) (b) : succ b ≠ a := fun hb => not_is_max b (h b hb)

@[simp]
theorem not_is_succ_limit_succ (a : α) : ¬IsSuccLimit (succ a) := fun h => h.succ_ne _ rfl

theorem is_succ_limit_iff_succ_ne : IsSuccLimit a ↔ ∀ b, succ b ≠ a :=
  ⟨IsSuccLimit.succ_ne, is_succ_limit_of_succ_ne⟩

theorem not_is_succ_limit_iff' : ¬IsSuccLimit a ↔ a ∈ Range (@succ α _ _) := by
  simp_rw [is_succ_limit_iff_succ_ne, not_forall, not_ne_iff]
  rfl

end NoMaxOrder

section OrderBot

variable [OrderBot α]

theorem is_succ_limit_bot : IsSuccLimit (⊥ : α) :=
  is_min_bot.IsSuccLimit

end OrderBot

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

theorem not_is_succ_limit_of_no_max [NoMinOrder α] [NoMaxOrder α] : ¬IsSuccLimit a := by
  simp

end IsSuccArchimedean

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α] [SuccOrder α]

theorem IsSuccLimit.succ_lt (hb : IsSuccLimit b) (ha : a < b) : succ a < b := by
  by_cases' h : IsMax a
  · rwa [h.succ_eq]
    
  · rw [lt_iff_le_and_neₓ, succ_le_iff_of_not_is_max h]
    refine' ⟨ha, fun hab => _⟩
    subst hab
    exact (h hb.is_max).elim
    

theorem IsSuccLimit.succ_lt_iff (hb : IsSuccLimit b) : succ a < b ↔ a < b :=
  ⟨fun h => (le_succ a).trans_lt h, hb.succ_lt⟩

theorem is_succ_limit_iff_succ_lt : IsSuccLimit b ↔ ∀ a < b, succ a < b :=
  ⟨fun hb a => hb.succ_lt, is_succ_limit_of_succ_lt⟩

theorem is_succ_limit_rec_on_succ' {C : α → Sort _} (hs : ∀ a, ¬IsMax a → C (succ a)) (hl : ∀ a, IsSuccLimit a → C a)
    {b : α} (hb : ¬IsMax b) : @isSuccLimitRecOn α _ _ C (succ b) hs hl = hs b hb := by
  have hb' := not_is_succ_limit_succ_of_not_is_max hb
  have H := Classical.some_spec (not_is_succ_limit_iff.1 hb')
  rw [is_succ_limit_rec_on]
  simp only [cast_eq_iff_heq, hb', not_false_iff, eq_mpr_eq_cast, dif_neg]
  congr
  · exact (succ_eq_succ_iff_of_not_is_max H.1 hb).1 H.2
    
  · apply proof_irrel_heq
    

section NoMaxOrder

variable [NoMaxOrder α]

@[simp]
theorem is_succ_limit_rec_on_succ {C : α → Sort _} (hs : ∀ a, ¬IsMax a → C (succ a)) (hl : ∀ a, IsSuccLimit a → C a)
    (b : α) : @isSuccLimitRecOn α _ _ C (succ b) hs hl = hs b (not_is_max b) :=
  is_succ_limit_rec_on_succ' _ _ _

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

theorem not_is_succ_limit [NoMinOrder α] : ¬IsSuccLimit a := by
  simp

end IsSuccArchimedean

end PartialOrderₓ

/-! ### Predecessor limits -/


section Preorderₓ

variable [Preorderₓ α] [PredOrder α]

/-- A predecessor limit is a value that isn't a predecessor, except possibly of itself. -/
def IsPredLimit (a : α) : Prop :=
  ∀ b, pred b = a → IsMin b

protected theorem IsPredLimit.is_min (h : IsPredLimit (pred a)) : IsMin a :=
  h a rfl

theorem not_is_pred_limit_pred_of_not_is_min (ha : ¬IsMin a) : ¬IsPredLimit (pred a) := fun h => ha (h a rfl)

protected theorem _root_.is_max.is_pred_limit : IsMax a → IsPredLimit a :=
  @IsMin.is_succ_limit αᵒᵈ a _ _

theorem is_pred_limit_of_pred_ne (h : ∀ b, pred b ≠ a) : IsPredLimit a := fun b hb => (h _ hb).elim

theorem not_is_pred_limit_iff : ¬IsPredLimit a ↔ ∃ b, ¬IsMin b ∧ pred b = a :=
  @not_is_succ_limit_iff αᵒᵈ _ _ _

/-- See `order.not_is_pred_limit_iff` for a version that states that `a` is a predecessor of a value
other than itself. -/
theorem mem_range_pred_of_not_is_pred_limit : ¬IsPredLimit a → a ∈ Range (@pred α _ _) :=
  @mem_range_succ_of_not_is_succ_limit αᵒᵈ _ _ _

theorem is_pred_limit_of_lt_pred : (∀ b > a, a < pred b) → IsPredLimit a :=
  @is_succ_limit_of_succ_lt αᵒᵈ a _ _

/-- A value can be built by building it on predecessors and predecessor limits.

Note that you need a partial order for data built using this to behave nicely on successors. -/
@[elabAsElim]
noncomputable def isPredLimitRecOn :
    ∀ {C : α → Sort _} (b) (hs : ∀ a, ¬IsMin a → C (pred a)) (hl : ∀ a, IsPredLimit a → C a), C b :=
  @isSuccLimitRecOn αᵒᵈ _ _

theorem is_pred_limit_rec_on_limit :
    ∀ {C : α → Sort _} (hs : ∀ a, ¬IsMin a → C (pred a)) (hl : ∀ a, IsPredLimit a → C a) (hb : IsPredLimit b),
      @isPredLimitRecOn α _ _ C b hs hl = hl b hb :=
  @is_succ_limit_rec_on_limit αᵒᵈ b _ _

section NoMinOrder

variable [NoMinOrder α]

theorem IsPredLimit.pred_ne (h : IsPredLimit a) (b) : pred b ≠ a := fun hb => not_is_min b (h b hb)

@[simp]
theorem not_is_pred_limit_pred (a : α) : ¬IsPredLimit (pred a) := fun h => h.pred_ne _ rfl

theorem is_pred_limit_iff_pred_ne : IsPredLimit a ↔ ∀ b, pred b ≠ a :=
  @is_succ_limit_iff_succ_ne αᵒᵈ a _ _ _

theorem not_is_pred_limit_iff' : ¬IsPredLimit a ↔ a ∈ Range (@pred α _ _) :=
  @not_is_succ_limit_iff' αᵒᵈ a _ _ _

end NoMinOrder

section OrderTop

variable [OrderTop α]

theorem is_pred_limit_top : IsPredLimit (⊤ : α) :=
  is_max_top.IsPredLimit

end OrderTop

section IsPredArchimedean

variable [IsPredArchimedean α]

protected theorem IsPredLimit.is_max_of_no_min [NoMinOrder α] : IsPredLimit a → IsMax a :=
  @IsSuccLimit.is_min_of_no_max αᵒᵈ a _ _ _ _

@[simp]
theorem is_pred_limit_iff_of_no_min [NoMinOrder α] : IsPredLimit a ↔ IsMax a :=
  @is_succ_limit_iff_of_no_max αᵒᵈ a _ _ _ _

theorem not_is_pred_limit_of_no_min [NoMinOrder α] [NoMaxOrder α] : ¬IsPredLimit a := by
  simp

end IsPredArchimedean

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α] [PredOrder α]

theorem IsPredLimit.lt_pred : ∀ ha : IsPredLimit a, a < b → a < pred b :=
  @IsSuccLimit.succ_lt αᵒᵈ b a _ _

theorem IsPredLimit.lt_pred_iff : ∀ ha : IsPredLimit a, a < pred b ↔ a < b :=
  @IsSuccLimit.succ_lt_iff αᵒᵈ b a _ _

theorem is_pred_limit_iff_lt_pred : IsPredLimit a ↔ ∀ b > a, a < pred b :=
  @is_succ_limit_iff_succ_lt αᵒᵈ a _ _

theorem is_pred_limit_rec_on_pred' :
    ∀ {C : α → Sort _} (hs : ∀ a, ¬IsMin a → C (pred a)) (hl : ∀ a, IsPredLimit a → C a) {b : α} (hb : ¬IsMin b),
      @isPredLimitRecOn α _ _ C (pred b) hs hl = hs b hb :=
  @is_succ_limit_rec_on_succ' αᵒᵈ _ _

section NoMinOrder

variable [NoMinOrder α]

@[simp]
theorem is_pred_limit_rec_on_pred :
    ∀ {C : α → Sort _} (hs : ∀ a, ¬IsMin a → C (pred a)) (hl : ∀ a, IsPredLimit a → C a) (b : α),
      @isPredLimitRecOn α _ _ C (pred b) hs hl = hs b (not_is_min b) :=
  @is_succ_limit_rec_on_succ αᵒᵈ _ _ _

end NoMinOrder

section IsPredArchimedean

variable [IsPredArchimedean α]

protected theorem IsPredLimit.is_max : IsPredLimit a → IsMax a :=
  @IsSuccLimit.is_min αᵒᵈ a _ _ _

@[simp]
theorem is_pred_limit_iff : IsPredLimit a ↔ IsMax a :=
  @is_succ_limit_iff αᵒᵈ a _ _ _

theorem not_is_pred_limit [NoMaxOrder α] : ¬IsPredLimit a := by
  simp

end IsPredArchimedean

end PartialOrderₓ

end Order

