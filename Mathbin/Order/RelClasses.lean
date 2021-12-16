import Mathbin.Data.Sum 
import Mathbin.Order.Basic

/-!
# Unbundled relation classes

In this file we prove some properties of `is_*` classes defined in `init.algebra.classes`. The main
difference between these classes and the usual order classes (`preorder` etc) is that usual classes
extend `has_le` and/or `has_lt` while these classes take a relation as an explicit argument.

-/


universe u v

variable {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β → Prop}

open Function

theorem IsRefl.swap r [IsRefl α r] : IsRefl α (swap r) :=
  ⟨refl_of r⟩

theorem IsIrrefl.swap r [IsIrrefl α r] : IsIrrefl α (swap r) :=
  ⟨irrefl_of r⟩

theorem IsTrans.swap r [IsTrans α r] : IsTrans α (swap r) :=
  ⟨fun a b c h₁ h₂ => trans_of r h₂ h₁⟩

theorem IsAntisymm.swap r [IsAntisymm α r] : IsAntisymm α (swap r) :=
  ⟨fun a b h₁ h₂ => antisymm h₂ h₁⟩

theorem IsAsymm.swap r [IsAsymm α r] : IsAsymm α (swap r) :=
  ⟨fun a b h₁ h₂ => asymm_of r h₂ h₁⟩

theorem IsTotal.swap r [IsTotal α r] : IsTotal α (swap r) :=
  ⟨fun a b => (total_of r a b).swap⟩

theorem IsTrichotomous.swap r [IsTrichotomous α r] : IsTrichotomous α (swap r) :=
  ⟨fun a b =>
      by 
        simpa [swap, Or.comm, Or.left_comm] using trichotomous_of r a b⟩

theorem IsPreorder.swap r [IsPreorder α r] : IsPreorder α (swap r) :=
  { @IsRefl.swap α r _, @IsTrans.swap α r _ with  }

theorem IsStrictOrder.swap r [IsStrictOrder α r] : IsStrictOrder α (swap r) :=
  { @IsIrrefl.swap α r _, @IsTrans.swap α r _ with  }

theorem IsPartialOrder.swap r [IsPartialOrder α r] : IsPartialOrder α (swap r) :=
  { @IsPreorder.swap α r _, @IsAntisymm.swap α r _ with  }

theorem IsTotalPreorder.swap r [IsTotalPreorder α r] : IsTotalPreorder α (swap r) :=
  { @IsPreorder.swap α r _, @IsTotal.swap α r _ with  }

theorem IsLinearOrder.swap r [IsLinearOrder α r] : IsLinearOrder α (swap r) :=
  { @IsPartialOrder.swap α r _, @IsTotal.swap α r _ with  }

protected theorem IsAsymm.is_antisymm r [IsAsymm α r] : IsAntisymm α r :=
  ⟨fun x y h₁ h₂ => (asymm h₁ h₂).elim⟩

protected theorem IsAsymm.is_irrefl [IsAsymm α r] : IsIrrefl α r :=
  ⟨fun a h => asymm h h⟩

protected theorem IsTotal.is_trichotomous r [IsTotal α r] : IsTrichotomous α r :=
  ⟨fun a b => Or.left_comm.1 (Or.inr$ total_of r a b)⟩

instance [Preorderₓ α] : IsRefl α (· ≤ ·) :=
  ⟨le_reflₓ⟩

instance [Preorderₓ α] : IsRefl α (· ≥ ·) :=
  IsRefl.swap _

instance [Preorderₓ α] : IsTrans α (· ≤ ·) :=
  ⟨@le_transₓ _ _⟩

instance [Preorderₓ α] : IsTrans α (· ≥ ·) :=
  IsTrans.swap _

instance [Preorderₓ α] : IsPreorder α (· ≤ ·) :=
  {  }

instance [Preorderₓ α] : IsPreorder α (· ≥ ·) :=
  {  }

instance [Preorderₓ α] : IsIrrefl α (· < ·) :=
  ⟨lt_irreflₓ⟩

instance [Preorderₓ α] : IsIrrefl α (· > ·) :=
  IsIrrefl.swap _

instance [Preorderₓ α] : IsTrans α (· < ·) :=
  ⟨@lt_transₓ _ _⟩

instance [Preorderₓ α] : IsTrans α (· > ·) :=
  IsTrans.swap _

instance [Preorderₓ α] : IsAsymm α (· < ·) :=
  ⟨@lt_asymmₓ _ _⟩

instance [Preorderₓ α] : IsAsymm α (· > ·) :=
  IsAsymm.swap _

instance [Preorderₓ α] : IsAntisymm α (· < ·) :=
  IsAsymm.is_antisymm _

instance [Preorderₓ α] : IsAntisymm α (· > ·) :=
  IsAsymm.is_antisymm _

instance [Preorderₓ α] : IsStrictOrder α (· < ·) :=
  {  }

instance [Preorderₓ α] : IsStrictOrder α (· > ·) :=
  {  }

instance [PartialOrderₓ α] : IsAntisymm α (· ≤ ·) :=
  ⟨@le_antisymmₓ _ _⟩

instance [PartialOrderₓ α] : IsAntisymm α (· ≥ ·) :=
  IsAntisymm.swap _

instance [PartialOrderₓ α] : IsPartialOrder α (· ≤ ·) :=
  {  }

instance [PartialOrderₓ α] : IsPartialOrder α (· ≥ ·) :=
  {  }

instance [LinearOrderₓ α] : IsTotal α (· ≤ ·) :=
  ⟨le_totalₓ⟩

instance [LinearOrderₓ α] : IsTotal α (· ≥ ·) :=
  IsTotal.swap _

instance LinearOrderₓ.is_total_preorder [LinearOrderₓ α] : IsTotalPreorder α (· ≤ ·) :=
  by 
    infer_instance

instance [LinearOrderₓ α] : IsTotalPreorder α (· ≥ ·) :=
  {  }

instance [LinearOrderₓ α] : IsLinearOrder α (· ≤ ·) :=
  {  }

instance [LinearOrderₓ α] : IsLinearOrder α (· ≥ ·) :=
  {  }

instance [LinearOrderₓ α] : IsTrichotomous α (· < ·) :=
  ⟨lt_trichotomyₓ⟩

instance [LinearOrderₓ α] : IsTrichotomous α (· > ·) :=
  IsTrichotomous.swap _

instance [LinearOrderₓ α] : IsTrichotomous α (· ≤ ·) :=
  IsTotal.is_trichotomous _

instance [LinearOrderₓ α] : IsTrichotomous α (· ≥ ·) :=
  IsTotal.is_trichotomous _

instance OrderDual.is_total_le [LE α] [IsTotal α (· ≤ ·)] : IsTotal (OrderDual α) (· ≤ ·) :=
  @IsTotal.swap α _ _

theorem ne_of_irrefl {r} [IsIrrefl α r] : ∀ {x y : α}, r x y → x ≠ y
| _, _, h, rfl => irrefl _ h

theorem trans_trichotomous_left [IsTrans α r] [IsTrichotomous α r] {a b c : α} : ¬r b a → r b c → r a c :=
  by 
    intro h₁ h₂ 
    rcases trichotomous_of r a b with (h₃ | h₃ | h₃)
    exact trans h₃ h₂ 
    rw [h₃]
    exact h₂ 
    exfalso 
    exact h₁ h₃

theorem trans_trichotomous_right [IsTrans α r] [IsTrichotomous α r] {a b c : α} : r a b → ¬r c b → r a c :=
  by 
    intro h₁ h₂ 
    rcases trichotomous_of r b c with (h₃ | h₃ | h₃)
    exact trans h₁ h₃ 
    rw [←h₃]
    exact h₁ 
    exfalso 
    exact h₂ h₃

/-- Construct a partial order from a `is_strict_order` relation.

See note [reducible non-instances]. -/
@[reducible]
def partialOrderOfSO r [IsStrictOrder α r] : PartialOrderₓ α :=
  { le := fun x y => x = y ∨ r x y, lt := r, le_refl := fun x => Or.inl rfl,
    le_trans :=
      fun x y z h₁ h₂ =>
        match y, z, h₁, h₂ with 
        | _, _, Or.inl rfl, h₂ => h₂
        | _, _, h₁, Or.inl rfl => h₁
        | _, _, Or.inr h₁, Or.inr h₂ => Or.inr (trans h₁ h₂),
    le_antisymm :=
      fun x y h₁ h₂ =>
        match y, h₁, h₂ with 
        | _, Or.inl rfl, h₂ => rfl
        | _, h₁, Or.inl rfl => rfl
        | _, Or.inr h₁, Or.inr h₂ => (asymm h₁ h₂).elim,
    lt_iff_le_not_le :=
      fun x y =>
        ⟨fun h =>
            ⟨Or.inr h,
              not_orₓ
                (fun e =>
                  by 
                    rw [e] at h <;> exact irrefl _ h)
                (asymm h)⟩,
          fun ⟨h₁, h₂⟩ => h₁.resolve_left fun e => h₂$ e ▸ Or.inl rfl⟩ }

/-- This is basically the same as `is_strict_total_order`, but that definition has a redundant
assumption `is_incomp_trans α lt`. -/
@[algebra]
class IsStrictTotalOrder' (α : Type u) (lt : α → α → Prop) extends IsTrichotomous α lt, IsStrictOrder α lt : Prop

/-- Construct a linear order from an `is_strict_total_order'` relation.

See note [reducible non-instances]. -/
@[reducible]
def linearOrderOfSTO' r [IsStrictTotalOrder' α r] [∀ x y, Decidable ¬r x y] : LinearOrderₓ α :=
  { partialOrderOfSO r with
    le_total :=
      fun x y =>
        match y, trichotomous_of r x y with 
        | y, Or.inl h => Or.inl (Or.inr h)
        | _, Or.inr (Or.inl rfl) => Or.inl (Or.inl rfl)
        | _, Or.inr (Or.inr h) => Or.inr (Or.inr h),
    decidableLe :=
      fun x y =>
        decidableOfIff (¬r y x)
          ⟨fun h => ((trichotomous_of r y x).resolve_left h).imp Eq.symm id,
            fun h => h.elim (fun h => h ▸ irrefl_of _ _) (asymm_of r)⟩ }

theorem IsStrictTotalOrder'.swap r [IsStrictTotalOrder' α r] : IsStrictTotalOrder' α (swap r) :=
  { IsTrichotomous.swap r, IsStrictOrder.swap r with  }

instance [LinearOrderₓ α] : IsStrictTotalOrder' α (· < ·) :=
  {  }

/-- A connected order is one satisfying the condition `a < c → a < b ∨ b < c`.
  This is recognizable as an intuitionistic substitute for `a ≤ b ∨ b ≤ a` on
  the constructive reals, and is also known as negative transitivity,
  since the contrapositive asserts transitivity of the relation `¬ a < b`.  -/
@[algebra]
class IsOrderConnected (α : Type u) (lt : α → α → Prop) : Prop where 
  conn : ∀ a b c, lt a c → lt a b ∨ lt b c

theorem IsOrderConnected.neg_trans {r : α → α → Prop} [IsOrderConnected α r] {a b c} (h₁ : ¬r a b) (h₂ : ¬r b c) :
  ¬r a c :=
  mt (IsOrderConnected.conn a b c)$
    by 
      simp [h₁, h₂]

theorem is_strict_weak_order_of_is_order_connected [IsAsymm α r] [IsOrderConnected α r] : IsStrictWeakOrder α r :=
  { @IsAsymm.is_irrefl α r _ with trans := fun a b c h₁ h₂ => (IsOrderConnected.conn _ c _ h₁).resolve_right (asymm h₂),
    incomp_trans :=
      fun a b c ⟨h₁, h₂⟩ ⟨h₃, h₄⟩ => ⟨IsOrderConnected.neg_trans h₁ h₃, IsOrderConnected.neg_trans h₄ h₂⟩ }

instance (priority := 100) is_order_connected_of_is_strict_total_order' [IsStrictTotalOrder' α r] :
  IsOrderConnected α r :=
  ⟨fun a b c h => (trichotomous _ _).imp_right fun o => o.elim (fun e => e ▸ h) fun h' => trans h' h⟩

instance (priority := 100) is_strict_total_order_of_is_strict_total_order' [IsStrictTotalOrder' α r] :
  IsStrictTotalOrder α r :=
  { is_strict_weak_order_of_is_order_connected with  }

instance [LinearOrderₓ α] : IsStrictTotalOrder α (· < ·) :=
  by 
    infer_instance

instance [LinearOrderₓ α] : IsOrderConnected α (· < ·) :=
  by 
    infer_instance

instance [LinearOrderₓ α] : IsIncompTrans α (· < ·) :=
  by 
    infer_instance

instance [LinearOrderₓ α] : IsStrictWeakOrder α (· < ·) :=
  by 
    infer_instance

/-- An extensional relation is one in which an element is determined by its set
  of predecessors. It is named for the `x ∈ y` relation in set theory, whose
  extensionality is one of the first axioms of ZFC. -/
@[algebra]
class IsExtensional (α : Type u) (r : α → α → Prop) : Prop where 
  ext : ∀ a b, (∀ x, r x a ↔ r x b) → a = b

instance (priority := 100) is_extensional_of_is_strict_total_order' [IsStrictTotalOrder' α r] : IsExtensional α r :=
  ⟨fun a b H => ((@trichotomous _ r _ a b).resolve_left$ mt (H _).2 (irrefl a)).resolve_right$ mt (H _).1 (irrefl b)⟩

/-- A well order is a well-founded linear order. -/
@[algebra]
class IsWellOrder (α : Type u) (r : α → α → Prop) extends IsStrictTotalOrder' α r : Prop where 
  wf : WellFounded r

instance (priority := 100) IsWellOrder.is_strict_total_order {α} (r : α → α → Prop) [IsWellOrder α r] :
  IsStrictTotalOrder α r :=
  by 
    infer_instance

instance (priority := 100) IsWellOrder.is_extensional {α} (r : α → α → Prop) [IsWellOrder α r] : IsExtensional α r :=
  by 
    infer_instance

instance (priority := 100) IsWellOrder.is_trichotomous {α} (r : α → α → Prop) [IsWellOrder α r] : IsTrichotomous α r :=
  by 
    infer_instance

instance (priority := 100) IsWellOrder.is_trans {α} (r : α → α → Prop) [IsWellOrder α r] : IsTrans α r :=
  by 
    infer_instance

instance (priority := 100) IsWellOrder.is_irrefl {α} (r : α → α → Prop) [IsWellOrder α r] : IsIrrefl α r :=
  by 
    infer_instance

instance (priority := 100) IsWellOrder.is_asymm {α} (r : α → α → Prop) [IsWellOrder α r] : IsAsymm α r :=
  by 
    infer_instance

/-- Construct a decidable linear order from a well-founded linear order. -/
noncomputable def IsWellOrder.linearOrder (r : α → α → Prop) [IsWellOrder α r] : LinearOrderₓ α :=
  by 
    let this' := fun x y => Classical.dec ¬r x y 
    exact linearOrderOfSTO' r

instance EmptyRelation.is_well_order [Subsingleton α] : IsWellOrder α EmptyRelation :=
  { trichotomous := fun a b => Or.inr$ Or.inl$ Subsingleton.elimₓ _ _, irrefl := fun a => id,
    trans := fun a b c => False.elim, wf := ⟨fun a => ⟨_, fun y => False.elim⟩⟩ }

instance Nat.Lt.is_well_order : IsWellOrder ℕ (· < ·) :=
  ⟨Nat.lt_wf⟩

instance Sum.Lex.is_well_order [IsWellOrder α r] [IsWellOrder β s] : IsWellOrder (Sum α β) (Sum.Lex r s) :=
  { trichotomous :=
      fun a b =>
        by 
          cases a <;> cases b <;> simp  <;> apply trichotomous,
    irrefl :=
      fun a =>
        by 
          cases a <;> simp  <;> apply irrefl,
    trans :=
      fun a b c =>
        by 
          cases a <;> cases b <;> simp  <;> cases c <;> simp  <;> apply trans,
    wf := Sum.lex_wf IsWellOrder.wf IsWellOrder.wf }

instance Prod.Lex.is_well_order [IsWellOrder α r] [IsWellOrder β s] : IsWellOrder (α × β) (Prod.Lex r s) :=
  { trichotomous :=
      fun ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ =>
        match @trichotomous _ r _ a₁ b₁ with 
        | Or.inl h₁ => Or.inl$ Prod.Lex.left _ _ h₁
        | Or.inr (Or.inr h₁) => Or.inr$ Or.inr$ Prod.Lex.left _ _ h₁
        | Or.inr (Or.inl e) =>
          e ▸
            match @trichotomous _ s _ a₂ b₂ with 
            | Or.inl h => Or.inl$ Prod.Lex.right _ h
            | Or.inr (Or.inr h) => Or.inr$ Or.inr$ Prod.Lex.right _ h
            | Or.inr (Or.inl e) => e ▸ Or.inr$ Or.inl rfl,
    irrefl :=
      fun ⟨a₁, a₂⟩ h =>
        by 
          cases' h with _ _ _ _ h _ _ _ h <;> [exact irrefl _ h, exact irrefl _ h],
    trans :=
      fun a b c h₁ h₂ =>
        by 
          cases' h₁ with a₁ a₂ b₁ b₂ ab a₁ b₁ b₂ ab <;> cases' h₂ with _ _ c₁ c₂ bc _ _ c₂ bc
          ·
            exact Prod.Lex.left _ _ (trans ab bc)
          ·
            exact Prod.Lex.left _ _ ab
          ·
            exact Prod.Lex.left _ _ bc
          ·
            exact Prod.Lex.right _ (trans ab bc),
    wf := Prod.lex_wf IsWellOrder.wf IsWellOrder.wf }

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr ∈ » s)
/-- An unbounded or cofinal set -/
def Unbounded (r : α → α → Prop) (s : Set α) : Prop :=
  ∀ a, ∃ (b : _)(_ : b ∈ s), ¬r b a

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr ∈ » s)
/-- A bounded or final set -/
def Bounded (r : α → α → Prop) (s : Set α) : Prop :=
  ∃ a, ∀ b _ : b ∈ s, r b a

@[simp]
theorem not_bounded_iff {r : α → α → Prop} (s : Set α) : ¬Bounded r s ↔ Unbounded r s :=
  by 
    classical 
    simp only [Bounded, Unbounded, not_forall, not_exists, exists_prop, not_and, not_not]

@[simp]
theorem not_unbounded_iff {r : α → α → Prop} (s : Set α) : ¬Unbounded r s ↔ Bounded r s :=
  by 
    classical 
    rw [not_iff_comm, not_bounded_iff]

namespace Prod

instance is_refl_preimage_fst {r : α → α → Prop} [h : IsRefl α r] : IsRefl (α × α) (Prod.fst ⁻¹'o r) :=
  ⟨fun a => refl_of r a.1⟩

instance is_refl_preimage_snd {r : α → α → Prop} [h : IsRefl α r] : IsRefl (α × α) (Prod.snd ⁻¹'o r) :=
  ⟨fun a => refl_of r a.2⟩

instance is_trans_preimage_fst {r : α → α → Prop} [h : IsTrans α r] : IsTrans (α × α) (Prod.fst ⁻¹'o r) :=
  ⟨fun _ _ _ => trans_of r⟩

instance is_trans_preimage_snd {r : α → α → Prop} [h : IsTrans α r] : IsTrans (α × α) (Prod.snd ⁻¹'o r) :=
  ⟨fun _ _ _ => trans_of r⟩

end Prod

